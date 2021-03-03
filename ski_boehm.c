#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <gc.h>

typedef enum {
  APP,
  CON,
  COMB,
} tag_t;

typedef enum {
  S = 's',
  K = 'k',
  I = 'i',
  C = 'c',
  T = 't',
  H = 'h',
} comb_t;

typedef struct term_t {
  tag_t tag; // union type tag
  union {
    struct {
      struct term_t* left; // left branch
      struct term_t* right; // right branch
    };
    comb_t comb; // combinator literal
  };
} term_t;

term_t* root;

static inline term_t* new() {
  return GC_MALLOC(sizeof(term_t));
}

void read_file(term_t* val, FILE* file) {
  int inp = fgetc(file);

  switch (inp) {
    case '`':
      val->tag = APP;
      val->left = new();
      read_file(val->left, file);
      val->right = new();
      read_file(val->right, file);
      break;
    case '#':
      val->tag = CON;
      val->left = new();
      read_file(val->left, file);
      val->right = new();
      read_file(val->right, file);
      break;
    case '\n':
      break;
    default:
      val->tag = COMB;
      val->comb = inp;
      break;
  }
}

void print_term(term_t* val) {
  switch (val->tag) {
    case APP:
      putchar('(');
      print_term(val->left);
      print_term(val->right);
      putchar(')');
      break;
    case CON:
      print_term(val->left); 
      putchar(' ');
      print_term(val->right);
      break;
    default:
      putchar(val->comb);
      break;
  }
}

bool does_reduce(term_t* val) {
  while (true) {
    if (val->tag == APP) {
      if (val->left->tag == APP) {
        if (val->left->left->tag == APP) {
          if (val->left->left->left->comb == S) {
            return true;
          }
        } else if (val->left->left->comb == K) {
          return true;
        }
      } else if (val->left->comb == I) {
        return true;
      } else if (val->left->comb == H) {
        return true;
      } else if (val->left->comb == T) {
        return true;
      }

      val = val->left;
    } else if (val->tag == CON) {
      val = val->right;
    } else {
      return false;
    }
  }
}

int to_num(term_t* val) {
  int number = 0;

  while (true) {
    if (val->tag == CON && val->left->tag == COMB) {
      val = val->right;
      number += 1;
    } else {
      return number;
    }
  }
}

size_t sp = 0;
term_t* spine[4096 * 128];

term_t* pop() {
  return spine[sp--];
}

void push(term_t* val) {
  spine[++sp] = val;
}

static inline void step(term_t* val) {
  if (val->tag == APP) {
    if (val->left->tag == APP) {
      if (val->left->left->tag == APP) {
        if (val->left->left->left->comb == S) {
          term_t* x = val->left->left->right;
          term_t* y = val->left->right;
          term_t* z = val->right;

          val->left = new();

          val->left->tag = APP;
          val->left->left = x;
          val->left->right = z;

          val->right = new();

          val->right->tag = APP;
          val->right->left = y;
          val->right->right = z;
        }
      } else if (val->left->left->comb == K) {
        *val = *val->left->right;
      } else if (val->left->left->comb == C) {
        val->left = val->left->right;
        val->tag = CON;
      }
        
    } else if (val->left->comb == I) {
      *val = *val->right;
    } else if (val->left->comb == H) {
      *val = *val->left;
    } else if (val->left->comb == T) {
      *val = *val->right;
    }
  }
}

void reduce() {
  while (true) {
    if (does_reduce(spine[sp])) {
      if (spine[sp]->tag == CON) {
        push(spine[sp]->right);
      } else {
        push(spine[sp]->left);
      }
    } else {
      pop();
    }
    
    if (sp) {
      step(spine[sp]);
    } else {
      return;
    }
  }
}

int main(int argc, char* argv[]) {
  if (argc <= 1) {
    printf("no file provided\n");
    return 1;
  } else {
    GC_INIT();

    FILE* f = fopen(argv[1], "r");

    root = new();

    read_file(root, f);
    fclose(f);

    push(root);
    reduce();

    printf("number: %d\n", to_num(root));
    print_term(root);
    putchar('\n');

    return 0;
  }
}
