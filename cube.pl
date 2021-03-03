% --------------------------------------

:- op(500, fx, ∀).
:- op(500, fx, λ).
:- op(600, xfy, →).
:- op(650, xfx, :).
:- op(625, yfx, $).

% --------------------------------------

contains(Item, [Item | _]).
contains(Item, [_ | Rest]) :-
    contains(Item, Rest), !.

% --------------------------------------

index_of([X | _], X, zero).
index_of([_ | Xs], Element, succ(Index)) :-
    index_of(Xs, Element, Index), !.

% --------------------------------------

lookup_type(Key, [(Key : Val) | _], Val) :- !.
lookup_type(Key, [_ | Rest], Val) :-
    lookup_type(Key, Rest, Val), !.

lookup_bind(Key, [(Key = Val) | _], Val) :- !.
lookup_bind(Key, [_ | Rest], Val) :-
    lookup_bind(Key, Rest, Val), !.

% --------------------------------------

insert_type(Key, Val, Map, [(Key : Val) | Map]).

insert_bind(Key, Val, Map, [(Key = Val) | Map]).

% --------------------------------------

remove_type(Key, [(Key : _) | Rest], Rest).
remove_type(Key, [Pair | Rest], [Pair | Tmp]) :-
    remove_type(Key, Rest, Tmp), !.

remove_bind(Key, [(Key = _) | Rest], Rest).
remove_bind(Key, [Pair | Rest], [Pair | Tmp]) :-
    remove_bind(Key, Rest, Tmp), !.

% --------------------------------------

delete(_, [], []).
delete(Key, [Key | Rest], Rest).
delete(Key, [Val | Rest], [Val | Tmp]) :-
    delete(Key, Rest, Tmp), !.

% --------------------------------------

is_num(z).
is_num(s(X)) :- is_num(X).

is_type(type $ _).

% --------------------------------------

univ_lte(type, type).
univ_lte(type, type $ _).
univ_lte(type $ X, type $ X).
univ_lte(type $ z, type $ (s $ _)).
univ_lte(type $ (s $ X), type $ (s $ Y)) :-
  univ_lte(type $ X, type $ Y).

% --------------------------------------


type_check(_, type, type $ (s $ z)) :- !.

type_check(_, type $ N, type $ (s $ N)) :- !.

type_check(_, z, level) :- !.

type_check(_, s $ X, level) :-
  type_check(_, X, level), !.

type_check(_, level, type) :- !.

type_check(Env, Func $ Value, Result) :-
    type_check(Env, Func, ∀ (Arg : ArgType) → BodyType), !,
    type_check(Env, Value, ValueType),
    beta_eq(Env, ArgType, ValueType),
    substitute(Env, BodyType, Arg, Value, Result), !.

type_check(Env, λ (Name : Type) → Body, ∀ (PiName : Type) → BodyType) :-
    insert_type(Name, Type, Env, NewEnv),
    type_check(NewEnv, Body, BodyType),
    type_check(Env, ∀ (PiName : Type) → BodyType, _), !.

type_check(Env, ∀ (Name : Type) → BodyType, PiType) :-
    reduce_and_type_check(Env, Type, Intermediate),
    insert_type(Name, Type, Env, NewEnv),
    reduce_and_type_check(NewEnv, BodyType, PiType),
    univ_lte(Intermediate, PiType), !.

type_check(Env, Name, Result) :-
    lookup_type(Name, Env, Result), !.

% --------------------------------------

reduce_and_type_check(Env, Value, Result) :-
    type_check(Env, Value, Intermediate),
    reduce(Env, Intermediate, Result), !.

% --------------------------------------

beta_eq(Env, A, B) :-
    reduce(Env, A, AResult),
    reduce(Env, B, BResult),
    alpha_eq(Env, AResult, BResult).

% --------------------------------------

%reduce(Env, Var $ Value, Result) :-
%   atom(Var),
%    lookup_bind(Var, Env, Func),
%    reduce(Env, Func $ Value, Result).

reduce(_, z, z) :- !.

reduce(_, s $ X, s $ X) :-
    is_num(X), !.

reduce(Env, s $ X, s $ Y) :-
    reduce(Env, X, Y), !.

reduce(_, level, level) :- !.

reduce(_, type, type) :- !.

reduce(_, type(X), type(X)) :- !.

reduce(Env, (λ (Name : _) → Body) $ Value, Result) :-
    substitute(Env, Body, Name, Value, Intermediate),
    reduce(Env, Intermediate, Result), !.

reduce(Env, Term $ Value, Result) :-
    reduce(Env, Term, Func),
    reduce(Env, Func $ Value, Result), !.

reduce(Env, Value, Result) :-
    lookup_bind(Value, Env, Result), !.

reduce(_, Value, Value) :- !.

% --------------------------------------

free_vars(Func $ Value, Result) :-
    free_vars(Func, FuncFreeVars), !,
    free_vars(Value, ValueFreeVars), !,
    append(FuncFreeVars, ValueFreeVars, Result), !.

free_vars(λ (Name : Type) → Body, Result) :-
    free_vars(Type, VarsInType), !,
    free_vars(Body, VarsInBody), !,
    delete(Name, VarsInBody, FreeVarsInBody), !,
    append(VarsInType, FreeVarsInBody, Result), !.

free_vars(∀ (Name : Type) → Body, Result) :-
    free_vars(Type, VarsInType), !,
    free_vars(Body, VarsInBody), !,
    delete(Name, VarsInBody, FreeVarsInBody), !,
    append(VarsInType, FreeVarsInBody, Result), !.

free_vars(type, []) :- !.

free_vars(type(_), []) :- !.

free_vars(Name, [Name]) :- !.

% --------------------------------------

alpha_eq(Env, A, B) :-
    canon(Env, A, zero, Result), !,
    canon(Env, B, zero, Result), !.

% --------------------------------------

canon(Env, Func $ Value, Count, CanonFunc $ CanonValue) :-
    canon(Env, Func, Count, CanonFunc), !,
    canon(Env, Value, Count, CanonValue), !.

canon(Env, λ (Name : Type) → Body, Count, λ (Count : CanonType) → CanonSub) :-
    canon(Env, Type, Count, CanonType), !,
    substitute_var(Env, Body, Name, Count, Sub), !,
    canon(Env, Sub, succ(Count), CanonSub), !.

canon(Env, ∀ (Name : Type) → Body, Count, ∀ (Count : CanonType) → CanonSub) :-
    canon(Env, Type, Count, CanonType), !,
    substitute_var(Env, Body, Name, Count, Sub), !,
    canon(Env, Sub, succ(Count), CanonSub), !.

canon(_, type, _, type) :- !.

canon(_, type(N), _, type(N)).

canon(_, Name, _, Name).

% --------------------------------------

substitute(Env, Func $ Value, Current, New, FuncSub $ ValueSub) :-
    substitute(Env, Func, Current, New, FuncSub),
    substitute(Env, Value, Current, New, ValueSub).

substitute(Env, λ (Name : Type) → Body, Name, New, λ (Name : TypeSub) → Body) :-
    substitute(Env, Type, Name, New, TypeSub).

substitute(Env, ∀ (Name : Type) → Body, Name, New, ∀ (Name : TypeSub) → Body) :-
    substitute(Env, Type, Name, New, TypeSub).

substitute(Env, λ (Name : Type) → Body, Current, New, λ (Sym : TypeSub) → BodySub) :-
    free_vars(New, FreeVars),
    contains(Name, FreeVars),
    substitute(Env, Type, Current, New, TypeSub),
    substitute_var(Env, Body, Name, Sym, BodyVarSub),
    substitute(Env, BodyVarSub, Current, New, BodySub).

substitute(Env, ∀ (Name : Type) → Body, Current, New, ∀ (Sym : TypeSub) → BodySub) :-
    free_vars(New, FreeVars),
    contains(Name, FreeVars),
    substitute(Env, Type, Current, New, TypeSub),
    substitute_var(Env, Body, Name, Sym, BodyVarSub),
    substitute(Env, BodyVarSub, Current, New, BodySub).

substitute(Env, λ (Name : Type) → Body, Current, New, λ (Name : TypeSub) → BodySub) :-
    substitute(Env, Type, Current, New, TypeSub),
    substitute(Env, Body, Current, New, BodySub).

substitute(Env, ∀ (Name : Type) → Body, Current, New, ∀ (Name : TypeSub) → BodySub) :-
    substitute(Env, Type, Current, New, TypeSub),
    substitute(Env, Body, Current, New, BodySub).

substitute(_, type, _, _, type).

substitute(Env, type(N), Current, New, type(NSub)) :-
  substitute(Env, N, Current, New, NSub).

substitute(_, Name, Name, New, New).

substitute(_, Name, _, _, Name).

% --------------------------------------

substitute_var(Env, Func $ Value, Current, New, FuncSub $ ValueSub) :-
    substitute_var(Env, Func, Current, New, FuncSub),
    substitute_var(Env, Value, Current, New, ValueSub).

substitute_var(Env, λ (Name : Type) → Body, Current, New, λ (Name : TypeSub) → BodySub) :-
    substitute_var(Env, Type, Current, New, TypeSub),
    substitute_var(Env, Body, Current, New, BodySub).

substitute_var(Env, ∀ (Name : Type) → Body, Current, New, ∀ (Name : TypeSub) → BodySub) :-
    substitute_var(Env, Type, Current, New, TypeSub),
    substitute_var(Env, Body, Current, New, BodySub).

substitute_var(_, type, _, _, type).

substitute_var(Env, type(N), Current, New, type(NSub)) :-
  substitute_var(Env, N, Current, New, NSub).

substitute_var(_, Name, Name, New, New).

substitute_var(_, Name, _, _, Name).

% --------------------------------------

tc(Env, Term, Type) :- type_check(Env, Term, Type), !.

% --------------------------------------

test_check(Result) :-
    F = (λ (x : ∀ (_ : type) → type) → x) $ (λ (y : type) → y),
    A = (λ (x : ∀ (_ : type) → type) → x),
    B = (λ (y : type) → y),
    tc([], F, Result),
    tc([], A $ B, Result).

eq_test :-
    A = (λ (x : ∀ (_ : type) → type) → x) $ (λ (z : type) → z),
    B = (λ (a : ∀ (_ : type) → type) → a) $ (λ (c : type) → c),
    alpha_eq(A, B).

test_dep(R) :-
    T = (λ (x : bool) → x) $ true, 
    tc([(bool : type), (true : bool), (false : bool)], T, R).

eq_test_two :-
    A = λ (x : type) → λ (y : type) → x,
    B = λ (a : type) → λ (b : type) → a,
    alpha_eq(A, B).

% --------------------------------------

to_env(A ; B, [A | R], Main) :- to_env(B, R, Main), !.
to_env(A, [], A).

demo(Result : Type) :-
    Value = (
      bool : type;
      true : bool;
      false : bool;
      
      nat : type;
      zero : nat;
      succ : ∀ (t : nat) → nat;

      top : (type $ (s $ z));
      unit : top;

      id : ∀ (t : type) → ∀ (v : t) → t;
      id = λ (q : type) → λ (x : q) → x;

          
      iduniv : ∀ (i : level) → ∀ (t : type) → ∀ (v : (t $ i)) → (t $ i);
      iduniv = λ (x : level) → λ (y : type) → λ (z : (y $ x)) → z;
                                                
      id $ top $ unit
    ),
    to_env(Value, Env, Main),
    tc(Env, Main, Type),
    reduce(Env, Main, Result).
               
