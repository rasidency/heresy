#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdfil.h>
#include <limits.h>

unsigned long fingerprint(unsigned long value) {
  return (value ^ 1469598103934665603UL) * 1099511628211UL;
}

long encode(const unsigned char *source, long size, unsigned char *output) {
  long *heads = calloc(4096, sizeof(long));
  long *previous = calloc((unsigned long)size, sizeof(long));
  if (!heads || !previous) exit(2);
  long position = 0;
  long used = 0;
  long best = 0;
  long distance = 0;
  long length = 0;
  long candidate = 0;
  long hash = 0;
  long start = 0;
  long attempts = 0;
  long literals = 0;
  long literal_start = 0;
  while (position < size) {
    best = 0;
    distance = 0;
    if (position + 2 < size) {
      hash = ((source[position] * 251 + source[position + 1]) * 251 + source[position + 2]) & 4095;
      candidate = heads[hash] - 1;
      attempts = 0;
      while (candidate >= 0 && position - candidate <= 65535 && attempts < 64) {
        length = 0;
        while (length < 130 && position + length < size &&
            source[position + length] == source[candidate + length]) length++;
        if (length > best) { best = length; distance = position - candidate; }
        if (best == 130) break;
        candidate = previous[candidate] - 1;
        attempts++;
      }
    }
    start = position;
    if (best >= 4) {
      literals = 0;
      output[used++] = (unsigned char)(128 + best - 3);
      output[used++] = (unsigned char)distance;
      output[used++] = (unsigned char)(distance >> 8);
      position += best;
    } else {
      if (literals == 0) { literal_start = used; output[used++] = 0; }
      output[used++] = source[position++];
      literals++;
      output[literal_start] = (unsigned char)(literals - 1);
      if (literals == 128) literals = 0;
    }
    while (start < position) {
      if (start + 2 < size) {
        hash = ((source[start] * 251 + source[start + 1]) * 251 + source[start + 2]) & 4095;
        previous[start] = heads[hash];
        heads[hash] = start + 1;
      }
      start++;
    }
  }
  free(previous);
  free(heads);
  return used;
}

long decode(const unsigned char *source, long size, unsigned char *output, long capacity) {
  long used = 0;
  long i = 0;
  long length = 0;
  long distance = 0;
  long j = 0;
  unsigned char control = 0;
  while (i < size) {
    control = source[i++];
    if (control < 128) {
      length = control + 1;
      if (length > size - i || length > capacity - used) return -1;
      if (output) {
        for (j = 0; j < length; j++) output[used++] = source[i++];
      } else { i += length; used += length; }
    } else {
      if (size - i < 2) return -1;
      distance = source[i] | ((long)source[i + 1] << 8);
      i += 2;
      length = (control & 127) + 3;
      if (distance == 0 || distance > used || length > capacity - used) return -1;
      if (output) {
        for (j = 0; j < length; j++) {
          output[used] = output[used - distance];
          used++;
        }
      } else used += length;
    }
  }
  return used;
}

unsigned char *read_file(const char *path, long *size) {
  FILE *file = fopen(path, "rb");
  if (!file) { printf("Cannot open %s\n", path); exit(2); }
  long capacity = 4096;
  long used = 0;
  unsigned char *data = malloc((unsigned long)capacity);
  if (!data) exit(2);
  while (1) {
    long count = (long)fread(data + used, 1, (unsigned long)(capacity - used), file);
    used += count;
    if (count == 0) break;
    if (used == capacity) {
      if (capacity > LONG_MAX / 2) { puts("Input size overflows the host representation"); exit(2); }
      capacity *= 2;
      unsigned char *next = malloc((unsigned long)capacity);
      if (!next) exit(2);
      memcpy(next, data, (unsigned long)used);
      free(data);
      data = next;
    }
  }
  fclose(file);
  *size = used;
  return data;
}

void write_file(const char *path, const unsigned char *data, long size) {
  FILE *file = fopen(path, "wb");
  if (!file) { printf("Cannot create %s\n", path); exit(2); }
  if ((long)fwrite(data, 1, (unsigned long)size, file) != size || fclose(file) != 0) {
    puts("File write failed");
    exit(2);
  }
}

int file_mode(const char *mode, const char *input, const char *output) {
  int pack = strcmp(mode, "pack") == 0;
  if (!pack && strcmp(mode, "unpack") != 0) { puts("Expected pack or unpack"); return 2; }
  long input_size = 0;
  unsigned char *data = read_file(input, &input_size);
  unsigned char *result = 0;
  long output_size = 0;
  unsigned long digest = 0;
  if (pack) {
    if (input_size > (LONG_MAX - 12) / 2 || (unsigned long)input_size > (unsigned long)LONG_MAX / sizeof(long)) {
      puts("Encoded size overflows the host representation"); return 2;
    }
    result = malloc((unsigned long)(input_size * 2 + 12));
    if (!result) return 2;
    result[0] = 'H'; result[1] = 'R'; result[2] = 'L'; result[3] = 'Z';
    for (int i = 0; i < 8; i++) result[4 + i] = (unsigned char)((unsigned long)input_size >> (i * 8));
    output_size = 12 + encode(data, input_size, result + 12);
    for (long i = 0; i < input_size; i++) digest = fingerprint(digest ^ data[i]);
  } else {
    if (input_size < 12 || data[0] != 'H' || data[1] != 'R' || data[2] != 'L' || data[3] != 'Z') {
      puts("Invalid LZ77 header"); return 2;
    }
    unsigned long expected = 0;
    for (int i = 0; i < 8; i++) expected |= (unsigned long)data[4 + i] << (i * 8);
    if (expected > (unsigned long)LONG_MAX - 1) { puts("Output size overflows the host representation"); return 2; }
    if (decode(data + 12, input_size - 12, 0, (long)expected) != (long)expected) {
      puts("Invalid LZ77 stream"); return 2;
    }
    result = malloc(expected + 1);
    if (!result) return 2;
    output_size = decode(data + 12, input_size - 12, result, (long)expected);
    if (output_size != (long)expected) { puts("Invalid LZ77 stream"); return 2; }
    for (long i = 0; i < output_size; i++) digest = fingerprint(digest ^ result[i]);
  }
  write_file(output, result, output_size);
  printf("%s: %ld -> %ld bytes\n", pack ? "Pack" : "Unpack", input_size, output_size);
  printf("Content fingerprint: %016lx\n", digest);
  free(result);
  free(data);
  return 0;
}

int main(int argc, char **argv) {
  if (argc == 4) return file_mode(argv[1], argv[2], argv[3]);
  if (argc != 2) {
    puts("Usage: codec 'text'");
    return 2;
  }
  long size = (long)strlen(argv[1]);
  if (size > (LONG_MAX - 2) / 2 || (unsigned long)size > (unsigned long)LONG_MAX / sizeof(long)) return 2;
  unsigned char *compressed = malloc((unsigned long)(size * 2 + 2));
  unsigned char *restored = malloc((unsigned long)(size + 1));
  if (!compressed || !restored) return 2;
  long packed = encode((const unsigned char *)argv[1], size, compressed);
  long unpacked = decode(compressed, packed, restored, size);
  if (unpacked != size) return 2;
  restored[size] = 0;
  if (strcmp(argv[1], (const char *)restored) != 0) return 2;
  unsigned long digest = 0;
  for (long i = 0; i < size; i++) digest = fingerprint(digest ^ restored[i]);
  printf("LZ77 input:       %ld bytes\n", size);
  printf("Compressed:       %ld bytes\n", packed);
  printf("Restored:         %ld bytes\n", unpacked);
  if (size > 0) printf("Original size:    %ld percent\n", packed * 100 / size);
  printf("Fingerprint:     %016lx\n", digest);
  printf("Output capability: %ld bytes\n", (char *)zgetupper(restored) - (char *)zgetlower(restored));
  printf("Encoded prefix:  ");
  long shown = packed < 24 ? packed : 24;
  for (long i = 0; i < shown; i++) printf("%02x ", compressed[i]);
  puts("");
  puts("Round trip: byte-exact");
  free(compressed);
  free(restored);
  return 0;
}
