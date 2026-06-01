#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
#include <string.h>
#include <limits.h>

struct Instruction {
  int opcode;
  long operand;
};

struct Program {
  struct Instruction *code;
  long count;
  long capacity;
  const char *source;
  long cursor;
};

unsigned long fingerprint(unsigned long value) {
  return (value ^ 1469598103934665603UL) * 1099511628211UL;
}

long product(long left, long right) {
  if ((left > 0 && ((right > 0 && left > LONG_MAX / right) || (right < 0 && right < LONG_MIN / left))) ||
      (left < 0 && ((right > 0 && left < LONG_MIN / right) || (right < 0 && left < LONG_MAX / right)))) {
    puts("Multiplication overflows long"); exit(2);
  }
  return left * right;
}

long fibonacci(long n) {
  if (n < 0) {
    puts("Fibonacci argument must be nonnegative");
    exit(2);
  }
  if (n < 2) return n;
  long previous = 0;
  long current = 1;
  for (long i = 1; i < n; i++) {
    if (previous > LONG_MAX - current) { puts("Fibonacci result overflows long"); exit(2); }
    long next = previous + current;
    previous = current;
    current = next;
  }
  return current;
}

void whitespace(struct Program *program) {
  while (program->source[program->cursor] == ' ') program->cursor++;
}

void emit(struct Program *program, int opcode, long operand) {
  if (program->count == program->capacity) {
    if ((unsigned long)program->capacity > (unsigned long)LONG_MAX / 2 / sizeof(struct Instruction)) {
      puts("Instruction storage overflows the host representation"); exit(2);
    }
    long capacity = program->capacity * 2;
    struct Instruction *next = malloc(sizeof(struct Instruction) * (unsigned long)capacity);
    if (!next) exit(2);
    memcpy(next, program->code, sizeof(struct Instruction) * (unsigned long)program->count);
    free(program->code);
    program->code = next;
    program->capacity = capacity;
  }
  program->code[program->count].opcode = opcode;
  program->code[program->count].operand = operand;
  program->count++;
}

void expression(struct Program *program, int minimum);

void atom(struct Program *program) {
  whitespace(program);
  char token = program->source[program->cursor];
  if (token == '(') {
    program->cursor++;
    expression(program, 0);
    whitespace(program);
    if (program->source[program->cursor] != ')') {
      puts("Missing closing parenthesis");
      exit(2);
    }
    program->cursor++;
    return;
  }
  if (token == '-') {
    program->cursor++;
    emit(program, 0, 0);
    atom(program);
    emit(program, 2, 0);
    return;
  }
  const char *position = program->source + program->cursor;
  if (position[0] == 'f' && position[1] == 'i' && position[2] == 'b') {
    program->cursor += 3;
    whitespace(program);
    if (program->source[program->cursor] != '(') {
      puts("Expected fib(argument)");
      exit(2);
    }
    atom(program);
    emit(program, 6, 0);
    return;
  }
  if (token < '0' || token > '9') {
    printf("Expected an operand at byte %ld\n", program->cursor);
    exit(2);
  }
  long value = 0;
  while (1) {
    token = program->source[program->cursor];
    if (token < '0' || token > '9') break;
    if (value > (LONG_MAX - (token - '0')) / 10) {
      puts("Integer literal overflows long");
      exit(2);
    }
    value = value * 10 + (token - '0');
    program->cursor++;
  }
  emit(program, 0, value);
}

void expression(struct Program *program, int minimum) {
  atom(program);
  while (1) {
    whitespace(program);
    char token = program->source[program->cursor];
    int precedence = 0;
    int opcode = 0;
    if (token == '+') { precedence = 1; opcode = 1; }
    if (token == '-') { precedence = 1; opcode = 2; }
    if (token == '*') { precedence = 2; opcode = 3; }
    if (token == '/') { precedence = 2; opcode = 4; }
    if (token == '^') { precedence = 3; opcode = 5; }
    if (precedence == 0 || precedence < minimum) break;
    program->cursor++;
    expression(program, precedence + (opcode != 5));
    emit(program, opcode, 0);
  }
}

long evaluate(struct Program *program) {
  long *stack = malloc(sizeof(long) * (unsigned long)program->capacity);
  if (!stack) exit(2);
  long (*transform)(long) = fibonacci;
  long top = 0;
  unsigned long digest = 0;
  for (long i = 0; i < program->count; i++) {
    struct Instruction *instruction = &program->code[i];
    int opcode = instruction->opcode;
    if (opcode == 0) {
      stack[top++] = instruction->operand;
      printf("%03ld  PUSH  %ld\n", i, instruction->operand);
      continue;
    }
    if (top < 1) exit(2);
    if (opcode == 6) {
      stack[top - 1] = transform(stack[top - 1]);
      printf("%03ld  FIB   -> %ld\n", i, stack[top - 1]);
      continue;
    }
    if (top < 2) exit(2);
    long right = stack[--top];
    long left = stack[top - 1];
    long result = 0;
    const char *name = "";
    switch (opcode) {
      case 1:
        if ((right > 0 && left > LONG_MAX - right) || (right < 0 && left < LONG_MIN - right)) exit(2);
        result = left + right; name = "ADD"; break;
      case 2:
        if ((right > 0 && left < LONG_MIN + right) || (right < 0 && left > LONG_MAX + right)) exit(2);
        result = left - right; name = "SUB"; break;
      case 3: result = product(left, right); name = "MUL"; break;
      case 4:
        if (right == 0 || (left == LONG_MIN && right == -1)) exit(2);
        result = left / right; name = "DIV"; break;
      case 5: {
        if (right < 0) exit(2);
        result = 1;
        long factor = left;
        long exponent = right;
        while (exponent) {
          if (exponent & 1) result = product(result, factor);
          exponent >>= 1;
          if (exponent) factor = product(factor, factor);
        }
        name = "POW";
        break;
      }
      default: exit(2);
    }
    stack[top - 1] = result;
    digest = fingerprint(digest ^ (unsigned long)result);
    printf("%03ld  %s   %ld, %ld -> %ld\n", i, name, left, right, result);
  }
  if (top != 1) exit(2);
  long result = stack[0];
  printf("Bytecode fingerprint: %016lx\n", digest);
  free(stack);
  return result;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    puts("Usage: machine 'arithmetic expression'");
    return 2;
  }
  struct Program program;
  program.capacity = 256;
  program.count = 0;
  program.cursor = 0;
  program.source = argv[1];
  program.code = malloc(sizeof(struct Instruction) * (unsigned long)program.capacity);
  if (!program.code) return 2;
  printf("Instruction allocation: %ld bytes, capability valid: %d\n",
    (char *)zgetupper(program.code) - (char *)zgetlower(program.code),
    zhasvalidcap(program.code));
  expression(&program, 0);
  whitespace(&program);
  if (program.source[program.cursor] != 0) {
    printf("Unexpected token at byte %ld\n", program.cursor);
    free(program.code);
    return 2;
  }
  printf("Expression: %s\n", program.source);
  printf("Compiled %ld instructions\n\n", program.count);
  long result = evaluate(&program);
  printf("Result: %ld\n", result);
  free(program.code);
  return 0;
}
