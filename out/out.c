#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "include/gc.h"
typedef struct {
  int n;
  uintptr_t *args;
  uintptr_t (*fun_ptr)(uintptr_t[]);
} thunk;
typedef struct {
   uintptr_t *ptr;
 } ref;
thunk * id;
uintptr_t _S0(uintptr_t args[]);
uintptr_t _S0(uintptr_t args[])
{
    uintptr_t _x0;
    _x0 = (uintptr_t) args[0];
    return (uintptr_t) _x0;
}
int main()
{
    thunk * _x1 = GC_malloc(sizeof(thunk));
    id = _x1;
    *id = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S0};
    int _x2;
    thunk * _x4;
    int _x5;
    _x4 = (thunk *) id;
    _x5 = 41;
    thunk * _x3 = GC_malloc(sizeof(thunk));
    memcpy(_x3, _x4, sizeof(thunk));
    _x3->args = GC_malloc(sizeof(uintptr_t) * _x4->n);
    memcpy(_x3->args, _x4->args, sizeof(uintptr_t) * _x4->n);
    _x3->args[0] = (uintptr_t) _x5;
    _x2 = (int) (_x3->fun_ptr)(_x3->args);
    printf("%d\n", _x2);
    return 0;
}