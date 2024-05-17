(*
  This file contains definition of lisp's `mapcar` function (php's `array_map`).
  http://clhs.lisp.se/Body/f_mapc_.htm
  https://www.php.net/manual/en/function.array-map.php

  mapcar (\s x -> s ++ show x) (["aaa", "bbb"], [1, 2]) == ["aaa1", "bbb2"]
  mapcar (+ 1) ([1, 2]) == [2, 3]
 *)

Require Import List.

Set Universe Polymorphism.

(* Length-indexed list. *)
Module IList.
  Inductive t (A : Type) : nat -> Type :=
  | Nil : t A 0
  | Cons : forall n, A -> t A n -> t A (S n).

  Module Notations.
    Declare Scope ilist_scope.
    Delimit Scope ilist_scope with ilist.
    Bind Scope ilist_scope with t.

    Arguments Nil {A}%type_scope : assert.
    Arguments Cons {A}%type_scope {n}%nat_scope _ _%ilist_scope : assert.

    Infix "::" := Cons (at level 60, right associativity) : ilist_scope.
    Notation "[ ]" := Nil (format "[ ]") : ilist_scope.
    Notation "[ x ]" := (Cons x Nil) : ilist_scope.
    Notation "[ x ; y ; .. ; z ]" := (Cons x (Cons y .. (Cons z Nil) ..))
        : ilist_scope.
  End Notations.
End IList.
Definition IList := IList.t.

(* Specific heterogenous list indexed by the length of argument array. *)
Module HList.
  Import ListNotations.
  
  Inductive t : forall n, list Type -> Type :=
  | Nil : forall n, t n []
  | Cons : forall T n (ls : list Type), IList T n -> t n ls -> t n (T :: ls).

  Module Notations.
    Declare Scope hlist_scope.
    Delimit Scope hlist_scope with hlist.
    Bind Scope hlist_scope with t.

    Arguments t _%nat_scope _%list_scope : assert.
    Arguments Nil {_}%nat_scope : assert.
    Arguments Cons {_ _ _} _%ilist_scope _%hlist_scope : assert.

    Infix "::" := Cons (at level 60, right associativity) : hlist_scope.
    Notation "[ ]" := Nil (format "[ ]") : hlist_scope.
    Notation "[ x ]" := (Cons x Nil) : hlist_scope.
    Notation "[ x ; y ; .. ; z ]" := (Cons x (Cons y .. (Cons z Nil) ..))
        : hlist_scope.
  End Notations.

  Definition getTypes {n ts} (xs : t n ts) := ts.
End HList.
Definition HList := HList.t.

Import ListNotations.
Import IList.Notations.
Import HList.Notations.

Open Scope hlist_scope.

Definition testHList : HList 2 [ nat; bool; option nat ] :=
  [ [1; 2] ; [true; false] ; [Some 1; None] ].

Open Scope list_scope.

(* Building the type for our f *)
Fixpoint Tf tres (ts : list Type) : Type :=
  match ts with nil => tres | t :: ts => t -> Tf tres ts end.

Open Scope ilist_scope.

Fixpoint fs {ts tres} n (f : Tf tres ts) : IList (Tf tres ts) n :=
  match n with
  | O => []
  | S n => f :: fs n f
  end.

Fixpoint reduce
  {n t ts tres}
  (fs : IList (Tf tres (t::ts)) n) (args : IList t n) : IList (Tf tres ts) n :=
  match fs in IList.t _ n return IList.t _ n -> n = n -> _ with
  | [] => fun _ _ => []
  | f :: fs =>
      fun '(a :: args) e =>
        let args := let 'eq_refl := e in args in f a :: reduce fs args
  end args eq_refl.

Open Scope hlist_scope.

Fixpoint reduce_lists {n ts tres} (lists : HList n ts)
  : IList (Tf tres ts) n -> IList tres n :=
  match lists with
  | [] => fun res => res
  | as__t :: as__ts =>
      fun fs =>
        let fs := reduce fs as__t in
        reduce_lists as__ts fs
  end.

Definition mapcar1 {ts n tres} (lists : HList n ts) (f : Tf tres ts)
  : IList tres n :=
  let fs := fs n f in reduce_lists lists fs.

Arguments mapcar1 {_ _ _} lists%hlist_scope _.

Definition mapcar {ts n tres} (f : Tf tres ts) (lists : HList n ts) :=
  mapcar1 lists f.

Arguments mapcar {_ _ _} _ lists%hlist_scope.

(*
  Machinery below is needed to allow implicit conversions from usual `list`
  (including `String`) to our length-indexed `IList` and vice-versa.
*)
Open Scope list_scope.

Fixpoint list_to_ilist {A} (xs : list A) : IList A (length xs) :=
  match xs with
  | [] => []%ilist
  | x :: xs => (x :: list_to_ilist xs)%ilist
  end.

Fixpoint ilist_to_list {A n} (xs : IList A n) : list A :=
  match xs with
  | []%ilist => []
  | (x :: xs)%ilist => x :: ilist_to_list xs
  end.

Coercion list_to_ilistC {A} := @list_to_ilist A.
Coercion ilist_to_listC {A} := @ilist_to_list A.

(* Examples *)

Compute mapcar1 testHList
  (fun n b o =>
     n + if b then 1 else 0 + match o with Some x => x | None => 0 end).

Compute mapcar (ts := HList.getTypes testHList)
  (fun n b o =>
     n + if b then 1 else 0 + match o with Some x => x | None => 0 end) testHList.

(* Examples by @monk *)

Require Import Arith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.

Compute mapcar1 [ ["aaa"; "bbb"] ; ["1"; "2"] ] (fun s x => s ++ x).

Compute mapcar1 [ ["aaa"; "bbb"] ; [1; 2] ]
(fun s x => s ++ if (x <=? 1)%nat then "1" else "2").

Compute mapcar1 [[1; 2]] (fun x => x + 1).
