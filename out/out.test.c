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
typedef struct _t_Option _t_Option;
typedef struct { } _t_OptionNone;
typedef struct {
            uintptr_t x0;
        } _t_OptionSome;
struct _t_Option {
    int tag;
    union {
        _t_OptionNone None; _t_OptionSome Some;
    };
};
_t_Option * None;
thunk * Some;
typedef struct _t_Pair _t_Pair;
typedef struct {
            uintptr_t x0; uintptr_t x1;
        } _t_PairPair;
struct _t_Pair {
    int tag;
    union {
        _t_PairPair Pair;
    };
};
thunk * Pair;
typedef struct _t_Sum _t_Sum;
typedef struct {
            uintptr_t x0;
        } _t_SumInl;
typedef struct {
            uintptr_t x0;
        } _t_SumInr;
struct _t_Sum {
    int tag;
    union {
        _t_SumInl Inl; _t_SumInr Inr;
    };
};
thunk * Inl;
thunk * Inr;
thunk * proj1;
thunk * proj2;
typedef struct _t_List _t_List;
typedef struct { } _t_ListNil;
typedef struct {
            uintptr_t x0; uintptr_t x1;
        } _t_ListCons;
struct _t_List {
    int tag;
    union {
        _t_ListNil Nil; _t_ListCons Cons;
    };
};
_t_List * Nil;
thunk * Cons;
thunk * isnil;
thunk * head;
thunk * tail;
thunk * app;
thunk * concat;
thunk * length;
thunk * rev;
thunk * map;
thunk * id;
thunk * compose;
thunk * flip;
uintptr_t _S0(uintptr_t args[]);
uintptr_t _S0(uintptr_t args[])
{
    _t_Option * _x0;
    uintptr_t _x1;
    _x1 = (uintptr_t) args[0];
    _x0 = GC_malloc(sizeof(_t_Option *));
    _x0->tag = 1;
    _x0->Some = (_t_OptionSome) {.x0 = _x1};
    return (uintptr_t) _x0;
}
uintptr_t _S1(uintptr_t args[]);
uintptr_t _S1(uintptr_t args[])
{
    _t_Pair * _x2;
    uintptr_t _x3;
    uintptr_t _x4;
    _x3 = (uintptr_t) args[1];
    _x4 = (uintptr_t) args[0];
    _x2 = GC_malloc(sizeof(_t_Pair *));
    _x2->tag = 0;
    _x2->Pair = (_t_PairPair) {.x0 = _x3, .x1 = _x4};
    return (uintptr_t) _x2;
}
uintptr_t _S2(uintptr_t args[]);
uintptr_t _S2(uintptr_t args[])
{
    thunk * _x5;
    thunk * _x6 = GC_malloc(sizeof(thunk));
    _x5 = _x6;
    *_x5 = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S1};
    _x5->args[1] = (uintptr_t) args[0];
    return (uintptr_t) _x5;
}
uintptr_t _S3(uintptr_t args[]);
uintptr_t _S3(uintptr_t args[])
{
    _t_Sum * _x7;
    uintptr_t _x8;
    _x8 = (uintptr_t) args[0];
    _x7 = GC_malloc(sizeof(_t_Sum *));
    _x7->tag = 0;
    _x7->Inl = (_t_SumInl) {.x0 = _x8};
    return (uintptr_t) _x7;
}
uintptr_t _S4(uintptr_t args[]);
uintptr_t _S4(uintptr_t args[])
{
    _t_Sum * _x9;
    uintptr_t _x10;
    _x10 = (uintptr_t) args[0];
    _x9 = GC_malloc(sizeof(_t_Sum *));
    _x9->tag = 1;
    _x9->Inr = (_t_SumInr) {.x0 = _x10};
    return (uintptr_t) _x9;
}
uintptr_t _S5(uintptr_t args[]);
uintptr_t _S5(uintptr_t args[])
{
    uintptr_t _x11;
    _t_Pair * _x12;
    _x12 = (_t_Pair *) args[0];
    if (1 && 1)
    {
        uintptr_t x = (uintptr_t) _x12->Pair.x0;
        _x11 = (uintptr_t) x;
    }
    else
    {
    }
    return (uintptr_t) _x11;
}
uintptr_t _S6(uintptr_t args[]);
uintptr_t _S6(uintptr_t args[])
{
    uintptr_t _x13;
    _t_Pair * _x14;
    _x14 = (_t_Pair *) args[0];
    if (1 && 1)
    {
        uintptr_t y = (uintptr_t) _x14->Pair.x1;
        _x13 = (uintptr_t) y;
    }
    else
    {
    }
    return (uintptr_t) _x13;
}
uintptr_t _S7(uintptr_t args[]);
uintptr_t _S7(uintptr_t args[])
{
    _t_List * _x15;
    uintptr_t _x16;
    uintptr_t _x17;
    _x16 = (uintptr_t) args[1];
    _x17 = (uintptr_t) args[0];
    _x15 = GC_malloc(sizeof(_t_List *));
    _x15->tag = 1;
    _x15->Cons = (_t_ListCons) {.x0 = _x16, .x1 = _x17};
    return (uintptr_t) _x15;
}
uintptr_t _S8(uintptr_t args[]);
uintptr_t _S8(uintptr_t args[])
{
    thunk * _x18;
    thunk * _x19 = GC_malloc(sizeof(thunk));
    _x18 = _x19;
    *_x18 = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S7};
    _x18->args[1] = (uintptr_t) args[0];
    return (uintptr_t) _x18;
}
uintptr_t _S9(uintptr_t args[]);
uintptr_t _S9(uintptr_t args[])
{
    int _x20;
    _t_List * _x21;
    _x21 = (_t_List *) args[0];
    if (_x21->tag == 0)
    {
        _x20 = 1;
    }
    else if (1)
    {
        _x20 = 0;
    }
    else
    {
    }
    return (uintptr_t) _x20;
}
uintptr_t _S10(uintptr_t args[]);
uintptr_t _S10(uintptr_t args[])
{
    _t_Option * _x22;
    _t_List * _x23;
    _x23 = (_t_List *) args[0];
    if (_x23->tag == 0)
    {
        _x22 = (_t_Option *) None;
    }
    else if (_x23->tag == 1 && (1 && 1))
    {
        uintptr_t x = (uintptr_t) _x23->Cons.x0;
        thunk * _x25;
        uintptr_t _x26;
        _x25 = (thunk *) Some;
        _x26 = (uintptr_t) x;
        thunk * _x24 = GC_malloc(sizeof(thunk));
        memcpy(_x24, _x25, sizeof(thunk));
        _x24->args = GC_malloc(sizeof(uintptr_t) * _x25->n);
        memcpy(_x24->args, _x25->args, sizeof(uintptr_t) * _x25->n);
        _x24->args[0] = (uintptr_t) _x26;
        _x22 = (_t_Option *) (_x24->fun_ptr)(_x24->args);
    }
    else
    {
    }
    return (uintptr_t) _x22;
}
uintptr_t _S11(uintptr_t args[]);
uintptr_t _S11(uintptr_t args[])
{
    _t_List * _x27;
    _t_List * _x28;
    _x28 = (_t_List *) args[0];
    if (_x28->tag == 0)
    {
        _x27 = (_t_List *) Nil;
    }
    else if (_x28->tag == 1 && (1 && 1))
    {
        uintptr_t l_ = (uintptr_t) _x28->Cons.x1;
        _x27 = (_t_List *) l_;
    }
    else
    {
    }
    return (uintptr_t) _x27;
}
uintptr_t _S12(uintptr_t args[]);
uintptr_t _S12(uintptr_t args[])
{
    _t_List * _x29;
    _t_List * _x30;
    _x30 = (_t_List *) args[1];
    if (_x30->tag == 0)
    {
        _x29 = (_t_List *) args[0];
    }
    else if (_x30->tag == 1 && (1 && 1))
    {
        uintptr_t x = (uintptr_t) _x30->Cons.x0;
        uintptr_t l1_ = (uintptr_t) _x30->Cons.x1;
        thunk * _x32;
        _t_List * _x33;
        thunk * _x35;
        uintptr_t _x36;
        _x35 = (thunk *) Cons;
        _x36 = (uintptr_t) x;
        thunk * _x34 = GC_malloc(sizeof(thunk));
        memcpy(_x34, _x35, sizeof(thunk));
        _x34->args = GC_malloc(sizeof(uintptr_t) * _x35->n);
        memcpy(_x34->args, _x35->args, sizeof(uintptr_t) * _x35->n);
        _x34->args[0] = (uintptr_t) _x36;
        _x32 = (thunk *) (_x34->fun_ptr)(_x34->args);
        thunk * _x38;
        _t_List * _x39;
        thunk * _x41;
        _t_List * _x42;
        _x41 = (thunk *) args[2];
        _x42 = (_t_List *) l1_;
        thunk * _x40 = GC_malloc(sizeof(thunk));
        memcpy(_x40, _x41, sizeof(thunk));
        _x40->args = GC_malloc(sizeof(uintptr_t) * _x41->n);
        memcpy(_x40->args, _x41->args, sizeof(uintptr_t) * _x41->n);
        _x40->args[0] = (uintptr_t) _x42;
        _x38 = (thunk *) (_x40->fun_ptr)(_x40->args);
        _x39 = (_t_List *) args[0];
        thunk * _x37 = GC_malloc(sizeof(thunk));
        memcpy(_x37, _x38, sizeof(thunk));
        _x37->args = GC_malloc(sizeof(uintptr_t) * _x38->n);
        memcpy(_x37->args, _x38->args, sizeof(uintptr_t) * _x38->n);
        _x37->args[0] = (uintptr_t) _x39;
        _x33 = (_t_List *) (_x37->fun_ptr)(_x37->args);
        thunk * _x31 = GC_malloc(sizeof(thunk));
        memcpy(_x31, _x32, sizeof(thunk));
        _x31->args = GC_malloc(sizeof(uintptr_t) * _x32->n);
        memcpy(_x31->args, _x32->args, sizeof(uintptr_t) * _x32->n);
        _x31->args[0] = (uintptr_t) _x33;
        _x29 = (_t_List *) (_x31->fun_ptr)(_x31->args);
    }
    else
    {
    }
    return (uintptr_t) _x29;
}
uintptr_t _S13(uintptr_t args[]);
uintptr_t _S13(uintptr_t args[])
{
    thunk * _x43;
    thunk * _x44 = GC_malloc(sizeof(thunk));
    _x43 = _x44;
    *_x43 = (thunk) {3, GC_malloc(sizeof(uintptr_t) * 3), (uintptr_t (*)(uintptr_t[])) &_S12};
    _x43->args[1] = (uintptr_t) args[0];
    _x43->args[2] = (uintptr_t) args[1];
    return (uintptr_t) _x43;
}
uintptr_t _S14(uintptr_t args[]);
uintptr_t _S14(uintptr_t args[])
{
    _t_List * _x45;
    _t_List * _x46;
    _x46 = (_t_List *) args[0];
    if (_x46->tag == 0)
    {
        _x45 = (_t_List *) Nil;
    }
    else if (_x46->tag == 1 && (1 && 1))
    {
        _t_List * x = (_t_List *) _x46->Cons.x0;
        uintptr_t l_ = (uintptr_t) _x46->Cons.x1;
        thunk * _x48;
        _t_List * _x49;
        thunk * _x51;
        _t_List * _x52;
        _x51 = (thunk *) app;
        _x52 = (_t_List *) x;
        thunk * _x50 = GC_malloc(sizeof(thunk));
        memcpy(_x50, _x51, sizeof(thunk));
        _x50->args = GC_malloc(sizeof(uintptr_t) * _x51->n);
        memcpy(_x50->args, _x51->args, sizeof(uintptr_t) * _x51->n);
        _x50->args[0] = (uintptr_t) _x52;
        _x48 = (thunk *) (_x50->fun_ptr)(_x50->args);
        thunk * _x54;
        _t_List * _x55;
        _x54 = (thunk *) args[1];
        _x55 = (_t_List *) l_;
        thunk * _x53 = GC_malloc(sizeof(thunk));
        memcpy(_x53, _x54, sizeof(thunk));
        _x53->args = GC_malloc(sizeof(uintptr_t) * _x54->n);
        memcpy(_x53->args, _x54->args, sizeof(uintptr_t) * _x54->n);
        _x53->args[0] = (uintptr_t) _x55;
        _x49 = (_t_List *) (_x53->fun_ptr)(_x53->args);
        thunk * _x47 = GC_malloc(sizeof(thunk));
        memcpy(_x47, _x48, sizeof(thunk));
        _x47->args = GC_malloc(sizeof(uintptr_t) * _x48->n);
        memcpy(_x47->args, _x48->args, sizeof(uintptr_t) * _x48->n);
        _x47->args[0] = (uintptr_t) _x49;
        _x45 = (_t_List *) (_x47->fun_ptr)(_x47->args);
    }
    else
    {
    }
    return (uintptr_t) _x45;
}
uintptr_t _S15(uintptr_t args[]);
uintptr_t _S15(uintptr_t args[])
{
    int _x56;
    _t_List * _x57;
    _x57 = (_t_List *) args[0];
    if (_x57->tag == 0)
    {
        _x56 = 0;
    }
    else if (_x57->tag == 1 && (1 && 1))
    {
        uintptr_t l_ = (uintptr_t) _x57->Cons.x1;
        int _x58;
        int _x59;
        _x58 = 1;
        thunk * _x61;
        _t_List * _x62;
        _x61 = (thunk *) args[1];
        _x62 = (_t_List *) l_;
        thunk * _x60 = GC_malloc(sizeof(thunk));
        memcpy(_x60, _x61, sizeof(thunk));
        _x60->args = GC_malloc(sizeof(uintptr_t) * _x61->n);
        memcpy(_x60->args, _x61->args, sizeof(uintptr_t) * _x61->n);
        _x60->args[0] = (uintptr_t) _x62;
        _x59 = (int) (_x60->fun_ptr)(_x60->args);
        _x56 = _x58 + _x59;
    }
    else
    {
    }
    return (uintptr_t) _x56;
}
uintptr_t _S16(uintptr_t args[]);
uintptr_t _S16(uintptr_t args[])
{
    _t_List * _x63;
    _t_List * _x64;
    _x64 = (_t_List *) args[0];
    if (_x64->tag == 0)
    {
        _x63 = (_t_List *) Nil;
    }
    else if (_x64->tag == 1 && (1 && 1))
    {
        uintptr_t x = (uintptr_t) _x64->Cons.x0;
        uintptr_t l_ = (uintptr_t) _x64->Cons.x1;
        thunk * _x66;
        _t_List * _x67;
        thunk * _x69;
        _t_List * _x70;
        _x69 = (thunk *) app;
        thunk * _x72;
        _t_List * _x73;
        _x72 = (thunk *) args[1];
        _x73 = (_t_List *) l_;
        thunk * _x71 = GC_malloc(sizeof(thunk));
        memcpy(_x71, _x72, sizeof(thunk));
        _x71->args = GC_malloc(sizeof(uintptr_t) * _x72->n);
        memcpy(_x71->args, _x72->args, sizeof(uintptr_t) * _x72->n);
        _x71->args[0] = (uintptr_t) _x73;
        _x70 = (_t_List *) (_x71->fun_ptr)(_x71->args);
        thunk * _x68 = GC_malloc(sizeof(thunk));
        memcpy(_x68, _x69, sizeof(thunk));
        _x68->args = GC_malloc(sizeof(uintptr_t) * _x69->n);
        memcpy(_x68->args, _x69->args, sizeof(uintptr_t) * _x69->n);
        _x68->args[0] = (uintptr_t) _x70;
        _x66 = (thunk *) (_x68->fun_ptr)(_x68->args);
        thunk * _x75;
        _t_List * _x76;
        thunk * _x78;
        uintptr_t _x79;
        _x78 = (thunk *) Cons;
        _x79 = (uintptr_t) x;
        thunk * _x77 = GC_malloc(sizeof(thunk));
        memcpy(_x77, _x78, sizeof(thunk));
        _x77->args = GC_malloc(sizeof(uintptr_t) * _x78->n);
        memcpy(_x77->args, _x78->args, sizeof(uintptr_t) * _x78->n);
        _x77->args[0] = (uintptr_t) _x79;
        _x75 = (thunk *) (_x77->fun_ptr)(_x77->args);
        _x76 = (_t_List *) Nil;
        thunk * _x74 = GC_malloc(sizeof(thunk));
        memcpy(_x74, _x75, sizeof(thunk));
        _x74->args = GC_malloc(sizeof(uintptr_t) * _x75->n);
        memcpy(_x74->args, _x75->args, sizeof(uintptr_t) * _x75->n);
        _x74->args[0] = (uintptr_t) _x76;
        _x67 = (_t_List *) (_x74->fun_ptr)(_x74->args);
        thunk * _x65 = GC_malloc(sizeof(thunk));
        memcpy(_x65, _x66, sizeof(thunk));
        _x65->args = GC_malloc(sizeof(uintptr_t) * _x66->n);
        memcpy(_x65->args, _x66->args, sizeof(uintptr_t) * _x66->n);
        _x65->args[0] = (uintptr_t) _x67;
        _x63 = (_t_List *) (_x65->fun_ptr)(_x65->args);
    }
    else
    {
    }
    return (uintptr_t) _x63;
}
uintptr_t _S17(uintptr_t args[]);
uintptr_t _S17(uintptr_t args[])
{
    _t_List * _x80;
    _t_List * _x81;
    _x81 = (_t_List *) args[0];
    if (_x81->tag == 0)
    {
        _x80 = (_t_List *) Nil;
    }
    else if (_x81->tag == 1 && (1 && 1))
    {
        uintptr_t x = (uintptr_t) _x81->Cons.x0;
        uintptr_t l_ = (uintptr_t) _x81->Cons.x1;
        thunk * _x83;
        _t_List * _x84;
        thunk * _x86;
        uintptr_t _x87;
        _x86 = (thunk *) Cons;
        thunk * _x89;
        uintptr_t _x90;
        _x89 = (thunk *) args[1];
        _x90 = (uintptr_t) x;
        thunk * _x88 = GC_malloc(sizeof(thunk));
        memcpy(_x88, _x89, sizeof(thunk));
        _x88->args = GC_malloc(sizeof(uintptr_t) * _x89->n);
        memcpy(_x88->args, _x89->args, sizeof(uintptr_t) * _x89->n);
        _x88->args[0] = (uintptr_t) _x90;
        _x87 = (uintptr_t) (_x88->fun_ptr)(_x88->args);
        thunk * _x85 = GC_malloc(sizeof(thunk));
        memcpy(_x85, _x86, sizeof(thunk));
        _x85->args = GC_malloc(sizeof(uintptr_t) * _x86->n);
        memcpy(_x85->args, _x86->args, sizeof(uintptr_t) * _x86->n);
        _x85->args[0] = (uintptr_t) _x87;
        _x83 = (thunk *) (_x85->fun_ptr)(_x85->args);
        thunk * _x92;
        _t_List * _x93;
        thunk * _x95;
        thunk * _x96;
        _x95 = (thunk *) args[2];
        _x96 = (thunk *) args[1];
        thunk * _x94 = GC_malloc(sizeof(thunk));
        memcpy(_x94, _x95, sizeof(thunk));
        _x94->args = GC_malloc(sizeof(uintptr_t) * _x95->n);
        memcpy(_x94->args, _x95->args, sizeof(uintptr_t) * _x95->n);
        _x94->args[0] = (uintptr_t) _x96;
        _x92 = (thunk *) (_x94->fun_ptr)(_x94->args);
        _x93 = (_t_List *) l_;
        thunk * _x91 = GC_malloc(sizeof(thunk));
        memcpy(_x91, _x92, sizeof(thunk));
        _x91->args = GC_malloc(sizeof(uintptr_t) * _x92->n);
        memcpy(_x91->args, _x92->args, sizeof(uintptr_t) * _x92->n);
        _x91->args[0] = (uintptr_t) _x93;
        _x84 = (_t_List *) (_x91->fun_ptr)(_x91->args);
        thunk * _x82 = GC_malloc(sizeof(thunk));
        memcpy(_x82, _x83, sizeof(thunk));
        _x82->args = GC_malloc(sizeof(uintptr_t) * _x83->n);
        memcpy(_x82->args, _x83->args, sizeof(uintptr_t) * _x83->n);
        _x82->args[0] = (uintptr_t) _x84;
        _x80 = (_t_List *) (_x82->fun_ptr)(_x82->args);
    }
    else
    {
    }
    return (uintptr_t) _x80;
}
uintptr_t _S18(uintptr_t args[]);
uintptr_t _S18(uintptr_t args[])
{
    thunk * _x97;
    thunk * _x98 = GC_malloc(sizeof(thunk));
    _x97 = _x98;
    *_x97 = (thunk) {3, GC_malloc(sizeof(uintptr_t) * 3), (uintptr_t (*)(uintptr_t[])) &_S17};
    _x97->args[1] = (uintptr_t) args[0];
    _x97->args[2] = (uintptr_t) args[1];
    return (uintptr_t) _x97;
}
uintptr_t _S19(uintptr_t args[]);
uintptr_t _S19(uintptr_t args[])
{
    uintptr_t _x99;
    _x99 = (uintptr_t) args[0];
    return (uintptr_t) _x99;
}
uintptr_t _S20(uintptr_t args[]);
uintptr_t _S20(uintptr_t args[])
{
    uintptr_t _x100;
    thunk * _x102;
    uintptr_t _x103;
    _x102 = (thunk *) args[1];
    thunk * _x105;
    uintptr_t _x106;
    _x105 = (thunk *) args[2];
    _x106 = (uintptr_t) args[0];
    thunk * _x104 = GC_malloc(sizeof(thunk));
    memcpy(_x104, _x105, sizeof(thunk));
    _x104->args = GC_malloc(sizeof(uintptr_t) * _x105->n);
    memcpy(_x104->args, _x105->args, sizeof(uintptr_t) * _x105->n);
    _x104->args[0] = (uintptr_t) _x106;
    _x103 = (uintptr_t) (_x104->fun_ptr)(_x104->args);
    thunk * _x101 = GC_malloc(sizeof(thunk));
    memcpy(_x101, _x102, sizeof(thunk));
    _x101->args = GC_malloc(sizeof(uintptr_t) * _x102->n);
    memcpy(_x101->args, _x102->args, sizeof(uintptr_t) * _x102->n);
    _x101->args[0] = (uintptr_t) _x103;
    _x100 = (uintptr_t) (_x101->fun_ptr)(_x101->args);
    return (uintptr_t) _x100;
}
uintptr_t _S21(uintptr_t args[]);
uintptr_t _S21(uintptr_t args[])
{
    thunk * _x107;
    thunk * _x108 = GC_malloc(sizeof(thunk));
    _x107 = _x108;
    *_x107 = (thunk) {3, GC_malloc(sizeof(uintptr_t) * 3), (uintptr_t (*)(uintptr_t[])) &_S20};
    _x107->args[1] = (uintptr_t) args[0];
    _x107->args[2] = (uintptr_t) args[1];
    return (uintptr_t) _x107;
}
uintptr_t _S22(uintptr_t args[]);
uintptr_t _S22(uintptr_t args[])
{
    thunk * _x109;
    thunk * _x110 = GC_malloc(sizeof(thunk));
    _x109 = _x110;
    *_x109 = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S21};
    _x109->args[1] = (uintptr_t) args[0];
    return (uintptr_t) _x109;
}
uintptr_t _S23(uintptr_t args[]);
uintptr_t _S23(uintptr_t args[])
{
    uintptr_t _x111;
    thunk * _x113;
    uintptr_t _x114;
    thunk * _x116;
    uintptr_t _x117;
    _x116 = (thunk *) args[1];
    _x117 = (uintptr_t) args[0];
    thunk * _x115 = GC_malloc(sizeof(thunk));
    memcpy(_x115, _x116, sizeof(thunk));
    _x115->args = GC_malloc(sizeof(uintptr_t) * _x116->n);
    memcpy(_x115->args, _x116->args, sizeof(uintptr_t) * _x116->n);
    _x115->args[0] = (uintptr_t) _x117;
    _x113 = (thunk *) (_x115->fun_ptr)(_x115->args);
    _x114 = (uintptr_t) args[2];
    thunk * _x112 = GC_malloc(sizeof(thunk));
    memcpy(_x112, _x113, sizeof(thunk));
    _x112->args = GC_malloc(sizeof(uintptr_t) * _x113->n);
    memcpy(_x112->args, _x113->args, sizeof(uintptr_t) * _x113->n);
    _x112->args[0] = (uintptr_t) _x114;
    _x111 = (uintptr_t) (_x112->fun_ptr)(_x112->args);
    return (uintptr_t) _x111;
}
uintptr_t _S24(uintptr_t args[]);
uintptr_t _S24(uintptr_t args[])
{
    thunk * _x118;
    thunk * _x119 = GC_malloc(sizeof(thunk));
    _x118 = _x119;
    *_x118 = (thunk) {3, GC_malloc(sizeof(uintptr_t) * 3), (uintptr_t (*)(uintptr_t[])) &_S23};
    _x118->args[1] = (uintptr_t) args[1];
    _x118->args[2] = (uintptr_t) args[0];
    return (uintptr_t) _x118;
}
uintptr_t _S25(uintptr_t args[]);
uintptr_t _S25(uintptr_t args[])
{
    thunk * _x120;
    thunk * _x121 = GC_malloc(sizeof(thunk));
    _x120 = _x121;
    *_x120 = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S24};
    _x120->args[1] = (uintptr_t) args[0];
    return (uintptr_t) _x120;
}
int main()
{
    None = GC_malloc(sizeof(_t_Option *));
    None->tag = 0;
    None->None = (_t_OptionNone) {};
    thunk * _x122 = GC_malloc(sizeof(thunk));
    Some = _x122;
    *Some = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S0};
    thunk * _x123 = GC_malloc(sizeof(thunk));
    Pair = _x123;
    *Pair = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S2};
    thunk * _x124 = GC_malloc(sizeof(thunk));
    Inl = _x124;
    *Inl = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S3};
    thunk * _x125 = GC_malloc(sizeof(thunk));
    Inr = _x125;
    *Inr = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S4};
    thunk * _x126 = GC_malloc(sizeof(thunk));
    proj1 = _x126;
    *proj1 = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S5};
    thunk * _x127 = GC_malloc(sizeof(thunk));
    proj2 = _x127;
    *proj2 = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S6};
    Nil = GC_malloc(sizeof(_t_List *));
    Nil->tag = 0;
    Nil->Nil = (_t_ListNil) {};
    thunk * _x128 = GC_malloc(sizeof(thunk));
    Cons = _x128;
    *Cons = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S8};
    thunk * _x129 = GC_malloc(sizeof(thunk));
    isnil = _x129;
    *isnil = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S9};
    thunk * _x130 = GC_malloc(sizeof(thunk));
    head = _x130;
    *head = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S10};
    thunk * _x131 = GC_malloc(sizeof(thunk));
    tail = _x131;
    *tail = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S11};
    thunk * _x132 = GC_malloc(sizeof(thunk));
    app = _x132;
    *app = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S13};
    app->args[1] = (uintptr_t) app;
    thunk * _x133 = GC_malloc(sizeof(thunk));
    concat = _x133;
    *concat = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S14};
    concat->args[1] = (uintptr_t) concat;
    thunk * _x134 = GC_malloc(sizeof(thunk));
    length = _x134;
    *length = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S15};
    length->args[1] = (uintptr_t) length;
    thunk * _x135 = GC_malloc(sizeof(thunk));
    rev = _x135;
    *rev = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S16};
    rev->args[1] = (uintptr_t) rev;
    thunk * _x136 = GC_malloc(sizeof(thunk));
    map = _x136;
    *map = (thunk) {2, GC_malloc(sizeof(uintptr_t) * 2), (uintptr_t (*)(uintptr_t[])) &_S18};
    map->args[1] = (uintptr_t) map;
    thunk * _x137 = GC_malloc(sizeof(thunk));
    id = _x137;
    *id = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S19};
    thunk * _x138 = GC_malloc(sizeof(thunk));
    compose = _x138;
    *compose = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S22};
    thunk * _x139 = GC_malloc(sizeof(thunk));
    flip = _x139;
    *flip = (thunk) {1, GC_malloc(sizeof(uintptr_t) * 1), (uintptr_t (*)(uintptr_t[])) &_S25};
    int _x140;
    thunk * _x142;
    int _x143;
    _x142 = (thunk *) id;
    _x143 = 3;
    thunk * _x141 = GC_malloc(sizeof(thunk));
    memcpy(_x141, _x142, sizeof(thunk));
    _x141->args = GC_malloc(sizeof(uintptr_t) * _x142->n);
    memcpy(_x141->args, _x142->args, sizeof(uintptr_t) * _x142->n);
    _x141->args[0] = (uintptr_t) _x143;
    _x140 = (int) (_x141->fun_ptr)(_x141->args);
    printf("%d\n", _x140);
    return 0;
}