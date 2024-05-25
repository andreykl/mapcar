Require Import Coq.Program.Basics.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope program_scope.

(*
  Definition of Freer Monad. This is a basic construction for representing
  algebraic effects.

  Source https://okmij.org/ftp/Computation/free-monad.html .
*)
Module FFree.
  CoInductive t (G : Type -> Type) (A : Type) : Type :=
  | Pure : A -> t G A
  | Impure {X} : G X -> (X -> t G A) -> t G A.

  CoFixpoint bind {G A B} (m : t G A) (ka : A -> t G B) : t G B :=
    match m with
    | Pure _ _ a => ka a
    | Impure _ _ gx kx => Impure _ _ gx (fun x => bind (kx x) ka)
    end.

  Definition eta {G : Type -> Type} {A : Type} : G A -> t G A :=
    (flip (Impure _ _)) (Pure _ _).

  Module Notations.
    (* Declare Scope ffree_scope. *)
    (* Delimit Scope ffree_scope with ffree. *)
    Bind Scope type_scope with t.

    Arguments t _%type _%type : assert.
    Arguments Pure {G A}%type _ : assert.
    Arguments Impure {G A X}%type _ _ : assert.

    Notation "F >>= k" := (bind F k) (at level 40, left associativity).
    Notation "'return' x" := (Pure x) (at level 40).
    Notation "'let*' ' v ':=' m 'in' e" := (m >>= (fun v => e)) (at level 40, v pattern).
    Notation "'let*' v ':=' m 'in' e" := (m >>= (fun v => e)) (at level 40, v pattern).
  End Notations.
End FFree.
Definition FFree := FFree.t.

(*
   Definition of the mutex. Mutex can be either [L]ocked or [U]nlocked. Our
   mutex have two operations: [lock] and [unlock]. We can [lock] only [U]nlocked
   mutex, and [unlock] only a [L]ocked one.
 *)
Module Mutex.
  Variant State : Type := L (* Locked *) | U (* Unlocked *).

  (* Type for mutex itself. State of the mutex is wrote into its type. *)
  Variant t (state : State) : Type := Mutex (name : string).

  Arguments Mutex {_} name : assert.

  (*
     Bodies of both functions below are trivial. Pay attention to the types of
     the function.

     The [lock] can accept an [U]nlocked mutex only and return the [L]ocked one.
  *)
  Definition lock(m : t U) : t L := let 'Mutex n := m in Mutex n.

  (*
     The [unlock] can accept a [L]ocked mutex only and return the [U]nlocked
     one.
  *)
  Definition unlock(m : t L) : t U := let 'Mutex n := m in Mutex n.
End Mutex.
Definition Mutex := Mutex.t.

(*
  Writer actions for running our programs. For our [IO] below.
*)
Module WActions.
  Variant t : Type -> Type :=
    | Tell (_ : string) : t unit.

  Module Notations.
    Bind Scope type_scope with t.
    Arguments t _%type : assert.
  End Notations.
End WActions.
Definition WActions := WActions.t.

(*
  IO actions for our programs. For our [IO] monad below.
*)
Module IOActions.
  Variant t : Type -> Type :=
    | PutStrLn (_ : string) : t unit
    | Lock (_ : Mutex Mutex.U) : t (Mutex.t Mutex.L)
    | UnLock (_ : Mutex Mutex.L) : t (Mutex.t Mutex.U)
    (* 
       *** We haven't used 2 definitions below ever in our programs. ***

       We should have one [TryLock] which would return either locked mutex or
       not locked. But since this is simulation, we have 2 of them, one which
       really do the lock and one which fails to lock given mutex. Type is the
       same for both.
     *)
    | TryLockT (_ : Mutex Mutex.U) : t {S & Mutex S}
    | TryLockF (_ : Mutex Mutex.U) : t {S & Mutex S}.

  Module Notations.
    Bind Scope type_scope with t.
    Arguments t _%type : assert.
  End Notations.
End IOActions.
Definition IOActions := IOActions.t.

(*
  Simulation for [IO] monad. It is just a [Writer] monad and IO functions
  wrapped around it.
*)
Module IO.
  Import WActions.Notations.
  Import IOActions.Notations.
  Import FFree.Notations.

  Definition t := FFree.t (fun R => WActions R + IOActions R)%type.

  Definition pure {G A} := @FFree.Pure G A.

  Definition systemLog : string -> t unit :=
    FFree.eta ∘ inl ∘ WActions.Tell ∘ (fun s => "System log: " ++ s)%string.
  Definition programOutput : string -> t unit :=
    FFree.eta ∘ inl ∘ WActions.Tell ∘ (fun s => "Program output: " ++ s)%string.
  Definition putStrLn : string -> t unit := FFree.eta ∘ inr ∘ IOActions.PutStrLn.
  Definition lock : Mutex Mutex.U -> t (Mutex Mutex.L)
    := FFree.eta ∘ inr ∘ IOActions.Lock.
  Definition unlock : Mutex Mutex.L -> t (Mutex Mutex.U)
    := FFree.eta ∘ inr ∘ IOActions.UnLock.
  Definition tryLockT : Mutex Mutex.U -> t {S & Mutex S}
    := FFree.eta ∘ inr ∘ IOActions.TryLockT.
  Definition tryLockF : Mutex Mutex.U -> t {S & Mutex S}
    := FFree.eta ∘ inr ∘ IOActions.TryLockF.

  Fixpoint run {R} (fuel : nat) (m : t R) : (option R * list string) :=
    match fuel with
    | O => (None, ["System log: Error. No more fuel."%string])
    | S fuel =>
        match m with
        | FFree.Pure r =>
            (Some r, ["System log: Pure action with result."%string])
        | FFree.Impure action fxr =>
            match action with
            | inl wa =>
                (let 'WActions.Tell s in WActions.t T := wa return (T -> _) -> _
                 in fun f => let '(r, log) := run fuel (f tt) in (r, s :: log)) fxr
            | inr ioa =>
                match ioa in IOActions.t T return (T -> _) -> _ with
                | IOActions.PutStrLn s =>
                    fun f => run fuel (let* r := programOutput s in f r)
                | IOActions.Lock (Mutex.Mutex name as m) =>
                    fun f => run fuel
                            (let* _ := systemLog ("Mutex " ++ name ++
                                                    " is locked with lock.")
                             in f (Mutex.lock m))
                | IOActions.UnLock (Mutex.Mutex name as m) =>
                    fun f => run fuel
                            (let* _ := systemLog ("Mutex " ++ name ++
                                                    " is unlocked.")
                             in f (Mutex.unlock m))
                | IOActions.TryLockT (Mutex.Mutex name as m) =>
                    fun f => run fuel
                            (let* _ :=
                               systemLog ("Mutex " ++ name ++
                                            " is locked with tryLockT.")
                           in f (existT _ _ (Mutex.lock m)))
                | IOActions.TryLockF (Mutex.Mutex name as m) =>
                    fun f => run fuel
                            (let* _ :=
                               systemLog ("Try lock mutex " ++ name ++
                                            " with tryLockF. The mutex has " ++
                                            "not been locked.")
                           in f (existT _ _ m))
                end fxr
            end
        end
    end.
End IO.
Definition IO := IO.t.

(* 
   Definition of commands for our program.
*)
Module Program.
  Import Mutex.

  (* We will have 3 mutices within our program. *)
  Definition MuticesState : Type := State * State * State.

  (* 
     We can lock mutices only in next order: 1, 2, 3. We can
     unlock them only in next order 2, 1, 3.

     So, each our command have a `MuticesState` before its execution and a
     `MuticesState` after execution.
   *)
  Inductive t : forall A : Type, MuticesState -> MuticesState -> Type :=
  | LockMutex1 : t unit (U, U, U) (L, U, U)
  | LockMutex2 : t unit (L, U, U) (L, L, U)
  | LockMutex3 : t unit (L, L, U) (L, L, L)
  | UnlockMutex1 : t unit (L, U, L) (U, U, L)
  | UnlockMutex2 : t unit (L, L, L) (L, U, L)
  | UnlockMutex3 : t unit (U, U, L) (U, U, U)
  | PutStrLn {S1 S2 S3} (_ : string) : t unit (S1, S2, S3) (S1, S2, S3)
  | Pure {A S1 S2 S3} (res : A) : t A (S1, S2, S3) (S1, S2, S3)
  | Bind {A B S1 S2 S3 M1 M2 M3 F1 F2 F3}
    : t A (S1, S2, S3) (M1, M2, M3) ->
      (A -> t B (M1, M2, M3) (F1, F2, F3)) ->
      t B (S1, S2, S3) (F1, F2, F3).

  Module Notations.
    Declare Scope program_scope.
    Delimit Scope program_scope with program.
    Bind Scope program_scope with t.

    Notation "e1 ;; e2" := (Bind e1%program (fun _ => e2%program))%program
                             (at level 61, right associativity) : program_scope.
    Notation "'Return' x" := (Pure x) (at level 40) : program_scope.
  End Notations.

  Import FFree.Notations.

  Fixpoint run {A S1 S2 S3 F1 F2 F3} (p : t A (S1, S2, S3) (F1, F2, F3))
    : (Mutex.t S1 * Mutex.t S2 * Mutex.t S3)
      -> IO (A * (Mutex.t F1 * Mutex.t F2 * Mutex.t F3)%type) :=
    match p with
    | LockMutex1 =>
        fun '(m1, m2, m3) =>
          let* m1 := IO.lock m1 in IO.pure (tt, (m1, m2, m3))
    | LockMutex2 =>
        fun '(m1, m2, m3) =>
          let* m2 := IO.lock m2 in IO.pure (tt, (m1, m2, m3))
    | LockMutex3 =>
        fun '(m1, m2, m3) =>
          let* m3 := IO.lock m3 in IO.pure (tt, (m1, m2, m3))
    | UnlockMutex1 =>
        fun '(m1, m2, m3) =>
          let* m1 := IO.unlock m1 in IO.pure (tt, (m1, m2, m3))
    | UnlockMutex2 =>
        fun '(m1, m2, m3) =>
          let* m2 := IO.unlock m2 in IO.pure (tt, (m1, m2, m3))
    | UnlockMutex3 =>
        fun '(m1, m2, m3) =>
          let* m3 := IO.unlock m3 in IO.pure (tt, (m1, m2, m3))
    | PutStrLn s =>
        fun '(m1, m2, m3) =>
          let* _ := IO.putStrLn s in
          IO.pure (tt, (m1, m2, m3))
    | Pure res =>
        fun '(m1, m2, m3) => IO.pure (res, (m1, m2, m3))
    | Bind m k =>
        fun '(m1, m2, m3) =>
          let* '(res, (m1, m2, m3)) := run m (m1, m2, m3) in
          run (k res) (m1, m2, m3)
    end.
End Program.
Definition Program := Program.t.

Import FFree.Notations.

Import Program.
Import Program.Notations.

Open Scope program_scope.

Definition testOK : Program nat (Mutex.U, Mutex.U, Mutex.U) (Mutex.U, Mutex.U, Mutex.U) :=
  PutStrLn "start work" ;;
  LockMutex1 ;;
  LockMutex2 ;;
  LockMutex3 ;;
  PutStrLn "middle of the work" ;;
  UnlockMutex2 ;;
  UnlockMutex1 ;;
  UnlockMutex3 ;;
  PutStrLn "finish work" ;;
  Return 5.

Definition justReturn5TestOK : Program nat (Mutex.U, Mutex.U, Mutex.U) (Mutex.U, Mutex.U, Mutex.U) :=
  PutStrLn "start work" ;;
  PutStrLn "do not touch mutices at all, just returning 5" ;;
  Return 5.

Fail Definition testFailWrongOrder
  : Program nat (Mutex.U, Mutex.U, Mutex.U) (Mutex.U, Mutex.U, Mutex.U) :=
  PutStrLn "start work" ;;
  LockMutex1 ;;
  PutStrLn "try to unlock mutex 1 now" ;;
  UnlockMutex1 ;; (* Fail.. *)
  Return 5.

Definition IOProgram : IO _ :=
  Program.run testOK (Mutex.Mutex "1", Mutex.Mutex "2", Mutex.Mutex "3").

Open Scope string_scope.

Compute IO.run 1000 IOProgram.
