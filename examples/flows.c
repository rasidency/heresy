#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdfil.h>
#include <limits.h>

struct Flow {
  unsigned long source;
  unsigned long destination;
  unsigned int sport;
  unsigned int dport;
  int protocol;
  long forward;
  long reverse;
  long bytes;
  long payload;
  struct Flow *next;
  struct Flow *order;
};

unsigned long bucket(unsigned long key) {
  return (key * 11400714819323198485UL) & 255UL;
}

unsigned long word(const unsigned char *p, int big) {
  if (big) return ((unsigned long)p[0] << 24) | ((unsigned long)p[1] << 16) |
    ((unsigned long)p[2] << 8) | p[3];
  return ((unsigned long)p[3] << 24) | ((unsigned long)p[2] << 16) |
    ((unsigned long)p[1] << 8) | p[0];
}

unsigned int half(const unsigned char *p) {
  return ((unsigned int)p[0] << 8) | p[1];
}

void reject(long position, const char *reason) {
  printf("Rejected at byte %ld: %s\n", position, reason);
  exit(2);
}

void endpoint(unsigned long address, unsigned int port) {
  printf("%lu.%lu.%lu.%lu:%u", (address >> 24) & 255UL,
    (address >> 16) & 255UL, (address >> 8) & 255UL, address & 255UL, port);
}

void application(const unsigned char *data, long length) {
  int request = length >= 4 && data[0] == 'G' && data[1] == 'E' && data[2] == 'T' && data[3] == ' ';
  int response = length >= 5 && data[0] == 'H' && data[1] == 'T' && data[2] == 'T' && data[3] == 'P' && data[4] == '/';
  if (!request && !response) return;
  printf("%s: ", request ? "Request" : "Response");
  for (long i = 0; i < length && i < 100; i++) {
    if (data[i] < 32 || data[i] > 126) break;
    putchar(data[i]);
  }
  putchar('\n');
}

int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    puts("Usage: flows capture.pcap [tcp|udp|all]");
    return 2;
  }
  int selected = 0;
  if (argc == 3) {
    if (strcmp(argv[2], "tcp") == 0) selected = 6;
    else if (strcmp(argv[2], "udp") == 0) selected = 17;
    else if (strcmp(argv[2], "all") != 0) return 2;
  }
  FILE *file = fopen(argv[1], "rb");
  if (!file) { printf("Cannot open %s\n", argv[1]); return 2; }
  long capacity = 4096;
  long size = 0;
  unsigned char *data = malloc((unsigned long)capacity);
  if (!data) return 2;
  while (1) {
    long count = (long)fread(data + size, 1, (unsigned long)(capacity - size), file);
    size += count;
    if (count == 0) break;
    if (size == capacity) {
      if (capacity > LONG_MAX / 2) reject(0, "Input size overflows the host representation");
      capacity *= 2;
      unsigned char *next = malloc((unsigned long)capacity);
      if (!next) return 2;
      memcpy(next, data, (unsigned long)size);
      free(data);
      data = next;
    }
  }
  fclose(file);
  if (size < 24) reject(0, "Truncated PCAP header");
  unsigned long magic = word(data, 0);
  int big = magic == 0xd4c3b2a1UL || magic == 0x4d3cb2a1UL;
  if (magic != 0xa1b2c3d4UL && magic != 0xa1b23c4dUL && !big) reject(0, "Unsupported PCAP magic");
  unsigned long version = word(data + 4, big);
  if ((!big && version != 0x00040002UL) || (big && version != 0x00020004UL)) reject(4, "Unsupported PCAP version");
  unsigned long snaplen = word(data + 16, big);
  if (snaplen == 0) reject(16, "Zero snapshot length");
  if ((word(data + 20, big) & 65535UL) != 1) reject(20, "Only Ethernet captures are supported");
  struct Flow **table = calloc(256, sizeof(struct Flow *));
  if (!table) return 2;
  struct Flow *head = 0;
  struct Flow *tail = 0;
  long position = 24;
  long records = 0;
  long packets = 0;
  long captured_bytes = 0;
  long tcp = 0;
  long udp = 0;
  long skipped = 0;
  long flow_count = 0;
  while (position < size) {
    if (size - position < 16) reject(position, "Truncated record header");
    unsigned long captured = word(data + position + 8, big);
    unsigned long original = word(data + position + 12, big);
    if (captured > snaplen || captured > original) reject(position, "Invalid record lengths");
    if (captured > (unsigned long)(size - position - 16)) reject(position, "Record extends beyond file");
    const unsigned char *frame = data + position + 16;
    position += 16 + (long)captured;
    records++;
    captured_bytes += (long)captured;
    if (captured < 14) reject(position - (long)captured, "Truncated Ethernet header");
    long link = 14;
    unsigned int ether = half(frame + 12);
    for (int tag = 0; tag < 2 && (ether == 0x8100 || ether == 0x88a8); tag++) {
      if (captured < (unsigned long)(link + 4)) reject(position, "Truncated VLAN header");
      ether = half(frame + link + 2);
      link += 4;
    }
    if (ether != 0x0800) { skipped++; continue; }
    if (captured < (unsigned long)(link + 20)) reject(position, "Truncated IPv4 header");
    const unsigned char *ip = frame + link;
    long ihl = (ip[0] & 15) * 4;
    long ip_size = half(ip + 2);
    if ((ip[0] >> 4) != 4 || ihl < 20 || ip_size < ihl || captured < (unsigned long)(link + ihl)) reject(position, "Invalid IPv4 header");
    long available = (long)captured - link;
    if (available > ip_size) available = ip_size;
    int protocol = ip[9];
    if ((half(ip + 6) & 0x3fff) != 0 || (protocol != 6 && protocol != 17)) { skipped++; continue; }
    if (protocol == 6) tcp++;
    else udp++;
    if (selected != 0 && selected != protocol) continue;
    long minimum = protocol == 6 ? 20 : 8;
    if (available - ihl < minimum) reject(position, "Truncated transport header");
    const unsigned char *transport = ip + ihl;
    long header = protocol == 6 ? (transport[12] >> 4) * 4 : 8;
    if (header < minimum || header > available - ihl) reject(position, "Invalid transport header");
    long payload = available - ihl - header;
    if (protocol == 17) {
      long length = half(transport + 4);
      if (length < 8 || length > ip_size - ihl) reject(position, "Invalid UDP length");
      if (payload > length - 8) payload = length - 8;
    }
    unsigned long source = word(ip + 12, 1);
    unsigned long destination = word(ip + 16, 1);
    unsigned int sport = half(transport);
    unsigned int dport = half(transport + 2);
    int reverse = source > destination || (source == destination && sport > dport);
    if (reverse) {
      unsigned long swap = source; source = destination; destination = swap;
      unsigned int port = sport; sport = dport; dport = port;
    }
    unsigned long index = bucket(source ^ (destination << 1) ^ ((unsigned long)sport << 32) ^ dport ^ (unsigned long)protocol);
    struct Flow *flow = table[index];
    while (flow && (flow->source != source || flow->destination != destination || flow->sport != sport || flow->dport != dport || flow->protocol != protocol)) flow = flow->next;
    if (!flow) {
      flow = calloc(1, sizeof(struct Flow));
      if (!flow) return 2;
      flow->source = source; flow->destination = destination;
      flow->sport = sport; flow->dport = dport; flow->protocol = protocol;
      flow->next = table[index]; table[index] = flow;
      if (tail) tail->order = flow;
      else head = flow;
      tail = flow;
      flow_count++;
    }
    if (reverse) flow->reverse++;
    else flow->forward++;
    flow->bytes += (long)captured;
    flow->payload += payload;
    packets++;
    if (protocol == 6) application(transport + header, payload);
  }
  printf("PCAP: %ld records, %ld captured bytes\n", records, captured_bytes);
  printf("Protocols: TCP=%ld UDP=%ld Skipped=%ld\n", tcp, udp, skipped);
  printf("Selected: %ld packets in %ld bidirectional flows\n\n", packets, flow_count);
  struct Flow *flow = head;
  while (flow) {
    printf("%s ", flow->protocol == 6 ? "TCP" : "UDP");
    endpoint(flow->source, flow->sport);
    printf(" <> ");
    endpoint(flow->destination, flow->dport);
    printf("  packets=%ld/%ld bytes=%ld payload=%ld\n", flow->forward, flow->reverse, flow->bytes, flow->payload);
    struct Flow *next = flow->order;
    free(flow);
    flow = next;
  }
  free(table);
  free(data);
  return 0;
}
