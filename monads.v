Require Import String.
Open Scope string_scope.


(* Maybe Monad *)
Inductive Maybe (A : Type) : Type :=
  | Just : A -> Maybe A
  | Nothing : Maybe A.

Arguments Just {A} _.
Arguments Nothing {A}.

Definition maybe_return {A : Type} (x : A) : Maybe A :=
  Just x.

Definition maybe_bind {A B : Type} (m : Maybe A) (f : A -> Maybe B) : Maybe B :=
  match m with
  | Just x => f x
  | Nothing => Nothing
  end.

Definition isJust {A : Type} (m : Maybe A) : bool :=
  match m with
  | Just _ => true
  | Nothing => false
  end.

Definition isNothing {A : Type} (m : Maybe A) : bool :=
  match m with
  | Just _ => false
  | Nothing => true
  end.

Definition fromMaybe {A : Type} (default : A) (m : Maybe A) : A :=
  match m with
  | Just x => x
  | Nothing => default
  end.


(* Exception Monad *)
Inductive Exception (A : Type) : Type :=
  | Success : A -> Exception A
  | Failure : string -> Exception A.

Arguments Success {A} x.
Arguments Failure {A} x.

Check Success.
Definition exception_return {A : Type} (x : A) : Exception A :=
  Success x.

Check Failure.
Definition exception_bind {A B : Type} (m : Exception A) (f : A -> Exception B) : Exception B :=
  match m with
  | Success x => f x
  | Failure msg => Failure msg
  end.

Definition isSuccess {A : Type} (m : Exception A) : bool :=
  match m with
  | Success _ => true
  | Failure _ => false
  end.

Definition isFailure {A : Type} (m : Exception A) : bool :=
  match m with
  | Success _ => false
  | Failure _ => true
  end.

Definition fromException {A : Type} (default : A) (m : Exception A) : A :=
  match m with
  | Success x => x
  | Failure _ => default
  end.

Definition getErrorMessage {A : Type} (m : Exception A) : string :=
  match m with
  | Success _ => ""
  | Failure msg => msg
  end.

Definition throw {A : Type} (msg : string) : Exception A :=
  Failure msg.

Definition catch {A : Type} (m : Exception A) (handler : string -> Exception A) : Exception A :=
  match m with
  | Success x => Success x
  | Failure msg => handler msg
  end.

Definition finally {A B : Type} (m : Exception A) (cleanup : Exception B) : Exception A :=
  match m with
  | Success x => match cleanup with
                 | Success _ => Success x
                 | Failure msg => Failure msg
                 end
  | Failure msg => Failure msg
  end.


(* State Monad *)
Definition State (S A : Type) := S -> (A * S).

Definition state_return {S A : Type} (x : A) : State S A :=
  fun s => (x, s).

Definition state_bind {S A B : Type} (m : State S A) (f : A -> State S B) : State S B :=
  fun s =>
    let (a, s') := m s in
    f a s'.

Definition state_get {S : Type} : State S S :=
  fun s => (s, s).

Definition state_put {S : Type} (new_state : S) : State S unit :=
  fun _ => (tt, new_state).

Definition state_modify {S : Type} (f : S -> S) : State S unit :=
  fun s => (tt, f s).


(* Reader Monad *)
Definition Reader (R A : Type) := R -> A.

Definition reader_return {R A : Type} (x : A) : Reader R A :=
  fun _ => x.

Definition reader_bind {R A B : Type} (m : Reader R A) (f : A -> Reader R B) : Reader R B :=
  fun r => f (m r) r.

Definition ask {R : Type} : Reader R R := fun r => r.

Definition local {R A : Type} (f : R -> R) (m : Reader R A) : Reader R A :=
  fun r => m (f r).


(* Writer Monad *)
Definition Writer (A : Type) := (A * string)%type.

Definition writer_return {A : Type} (x : A) : Writer A :=
  (x, "").

Definition writer_bind {A B : Type} (m : Writer A) (f : A -> Writer B) : Writer B :=
  let (a, log1) := m in
  let (b, log2) := f a in
  (b, log1 ++ log2).

Definition tell (msg : string) : Writer unit :=
  (tt, msg).

Definition listen {A : Type} (m : Writer A) : Writer (A * string) :=
  let (a, log) := m in
  ((a, log), log).

Definition pass {A : Type} (m : Writer (A * (string -> string))) : Writer A :=
  let p := m in
  let a := fst (fst p) in
  let f := snd (fst p) in
  let log := snd p in
  (a, f log).


(* Identity Monad *)
Definition Identity (A : Type) := A.

Definition identity_return {A : Type} (x : A) : Identity A := x.

Definition identity_bind {A B : Type} (m : Identity A) (f : A -> Identity B) : Identity B :=
  f m.


(* Continuation Monad *)
Definition Cont (R A : Type) := (A -> R) -> R.

Definition cont_return {R A : Type} (x : A) : Cont R A :=
  fun k => k x.


(* Probabilistic Monad *)
Require Import List.
Import ListNotations.

Definition Prob (A : Type) := list A.

Definition prob_return {A : Type} (x : A) : Prob A :=
  [x].

Definition prob_bind {A B : Type} (m : Prob A) (f : A -> Prob B) : Prob B :=
  concat (map f m).



(* 

PROOFS OF MONAD LAWS 
1) Left Identity: bind (return x) f = f x
2) Right Identity: bind m return = m
3) Associativity: bind (bind m f) g = bind m (fun x => bind (f x) g)

*)



(* Monad laws for Maybe Monad *)

(* Left Identity *)
Lemma maybe_left_identity :
  forall (A B : Type) (x : A) (f : A -> Maybe B),
    maybe_bind (maybe_return x) f = f x.
Proof.
  intros. reflexivity.
Qed.


(* Right Identity *)
Lemma maybe_right_identity :
  forall (A : Type) (m : Maybe A),
    maybe_bind m maybe_return = m.
Proof.
  intros. destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


(* Associativity *)
Lemma maybe_associativity :
  forall (A B C : Type)
         (m : Maybe A)
         (f : A -> Maybe B)
         (g : B -> Maybe C),
    maybe_bind (maybe_bind m f) g = maybe_bind m (fun x => maybe_bind (f x) g).
Proof.
  intros. destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.



(* Monad laws for Exception Monad *)

(* Left Identity *)
Lemma exception_left_identity :
  forall (A B : Type) (x : A) (f : A -> Exception B),
    exception_bind (exception_return x) f = f x.
Proof.
  intros. reflexivity.
Qed.


(* Right Identity *)
Lemma exception_right_identity :
  forall (A : Type) (m : Exception A),
    exception_bind m exception_return = m.
Proof.
  intros. destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


(* Associativity *)
Lemma exception_associativity :
  forall (A B C : Type)
         (m : Exception A)
         (f : A -> Exception B)
         (g : B -> Exception C),
    exception_bind (exception_bind m f) g = exception_bind m (fun x => exception_bind (f x) g).
Proof.
  intros. destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.



(* Monad laws for State Monad *)

(* Left Identity *)
Lemma state_left_identity :
  forall (S A B : Type) (x : A) (f : A -> State S B),
    state_bind (state_return x) f = f x.
Proof.
  intros. reflexivity.
Qed.


(* Right Identity *)
Lemma state_right_identity :
  forall (S A : Type) (m : State S A) (s : S),
    state_bind m state_return s = m s.
Proof.
  intros. unfold state_bind, state_return.
  destruct (m s) as [a s'].
  reflexivity.
Qed.


(* Associativity *)
Lemma state_associativity :
  forall (S A B C : Type)
         (m : State S A)
         (f : A -> State S B)
         (g : B -> State S C)
         (s : S),
    state_bind (state_bind m f) g s = state_bind m (fun x => state_bind (f x) g) s.
Proof.
  intros. unfold state_bind. destruct m. reflexivity.
Qed.


(* Monad laws for Reader Monad *)

(* Left Identity *)
Lemma reader_left_identity :
  forall (R A B : Type) (x : A) (f : A -> Reader R B) (r : R),
    reader_bind (reader_return x) f r = f x r.
Proof.
  intros. reflexivity.
Qed.


(* Right Identity *)
Lemma reader_right_identity :
  forall (R A : Type) (m : Reader R A) (r : R),
    reader_bind m reader_return r = m r.
Proof.
  intros. reflexivity.
Qed.


(* Associativity *)
Lemma reader_associativity :
  forall (R A B C : Type)
         (m : Reader R A)
         (f : A -> Reader R B)
         (g : B -> Reader R C)
         (r : R),
    reader_bind (reader_bind m f) g r = reader_bind m (fun x => reader_bind (f x) g) r.
Proof.
  intros. reflexivity.
Qed.


(* Monad laws for Writer Monad *)


Require Import String.
Open Scope string_scope.


(* Helper Lemma to proof that: s ++ "" = s *)
Lemma string_append_empty_r : forall s : string, s ++ "" = s.
Proof.
  intros. induction s.
  - simpl. reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.


(* Helper Lemma to proof that: s ++ "" = s *)
Lemma string_append_assoc : forall a b c : string, (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  intros. induction a as [| a' s' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


(* Left Identity *)
Lemma writer_left_identity :
  forall (A B : Type) (x : A) (f : A -> Writer B),
    writer_bind (writer_return x) f = f x.
Proof.
  intros. simpl. destruct (f x) as [log2 b]. reflexivity.
Qed.


(* Right Identity *)
Lemma writer_right_identity :
  forall (A : Type) (m : Writer A),
    writer_bind m writer_return = m.
Proof.
  intros. unfold writer_bind, writer_return. destruct m. rewrite string_append_empty_r. reflexivity.
Qed.


(* Associativity *)
Lemma writer_associativity :
  forall (A B C : Type)
         (m : Writer A)
         (f : A -> Writer B)
         (g : B -> Writer C),
    writer_bind (writer_bind m f) g = writer_bind m (fun x => writer_bind (f x) g).
Proof.
  intros. unfold writer_bind, writer_return. 
  - destruct m as [a log1]. 
  destruct (f a) as [b log2]. 
  destruct (g b) as [c log3]. rewrite string_append_assoc.  reflexivity.
Qed.


(* Monad laws for Identity Monad *)

(* Left Identity *)
Lemma identity_left_identity :
  forall (A B : Type) (x : A) (f : A -> Identity B),
    identity_bind (identity_return x) f = f x.
Proof.
  intros. reflexivity.
Qed.


(* Right Identity *)
Lemma identity_right_identity :
  forall (A : Type) (m : Identity A),
    identity_bind m identity_return = m.
Proof.
  intros. reflexivity.
Qed.


(* Associativity *)
Lemma identity_associativity :
  forall (A B C : Type)
         (m : Identity A)
         (f : A -> Identity B)
         (g : B -> Identity C),
    identity_bind (identity_bind m f) g = identity_bind m (fun x => identity_bind (f x) g).
Proof.
  intros. reflexivity.
Qed.






(* This section contains examples that illustrate the practical usage of each monad that I implemented. 
  Each example is designed to show how the monad handles specific computational effects, such as 
  failure, state, or logging, using the helper functions defined earlier. *)




(* Maybe monad example: safe division and addition using the Maybe monad *)


Require Import PeanoNat.
Open Scope nat_scope.


Definition safeDivide (n m : nat) : Maybe nat :=
  if m =? 0 then Nothing else Just (n / m).

Definition plusMaybe (x y : Maybe nat) : Maybe nat :=
  maybe_bind x (fun a => maybe_bind y (fun b => maybe_return (a + b))).

Definition exampleMaybe := plusMaybe (safeDivide 10 2) (safeDivide 5 0).

Compute isJust exampleMaybe. (* Expected: false *)
Compute fromMaybe 0 exampleMaybe. (* Expected: 0,as result is Nothing *)


Lemma safeDivide_by_zero : safeDivide 5 0 = Nothing.
Proof. reflexivity. Qed.

Lemma plusMaybe_valid : plusMaybe (Just 3) (Just 4) = Just 7.
Proof. simpl. reflexivity. Qed.



(* Exception monad example: user login with error handling *)

Definition login (u p : string) : Exception string :=
  if String.eqb u "admin" then
    if String.eqb p "1234" then Success "Welcome!"
    else throw "Wrong password"
  else throw "User not found".

(* Attempt a login with wrong password *)
Definition exampleLogin1 := exception_bind (login "admin" "12345") 
  (fun msg => Success ("Access granted: " ++ msg)).

Compute getErrorMessage exampleLogin1.
(* Expected: "Wrong password" *)

(* Attempt a login with unknown user, and catch the error *)
Definition exampleLogin2 :=
  catch (login "guest" "1234") (fun err => Success ("Error: " ++ err)).

Compute fromException "" exampleLogin2.
(* Expected: "Error: User not found" *)


Lemma login_fail : login "admin" "wrong" = Failure "Wrong password".
Proof. reflexivity. Qed.

Lemma login_success : login "admin" "1234" = Success "Welcome!".
Proof. reflexivity. Qed.




(* State moonad example: an increment operation that returns the current state and adds 1 *)
Definition increment : State nat nat :=
  fun s => (s, s + 1).

Definition exampleState : State nat nat :=
  state_bind state_get (fun s =>
  state_bind (state_put (s + 1)) (fun _ =>
  state_return s)).

Compute exampleState 0.
(* Expected result: (0, 1) *)

Lemma exampleState_behavior : exampleState 1 = (1, 2).
Proof. reflexivity. Qed.


(* Reader monad example: get a personalized greeting *)
Definition getGreeting : Reader string string :=
  fun name => "Hello, " ++ name ++ "!".


Definition politeGreet : Reader string string :=
  reader_bind getGreeting (fun msg =>
  reader_bind ask (fun env =>
  reader_return (msg))).

Definition shoutGreeting : Reader string string :=
  local (fun _ => "ADMIN") getGreeting.

Compute politeGreet "Alice".
(* Expected: "Hello, Alice!" *)

Compute shoutGreeting "Bob".
(* Expected: "Hello, ADMIN!" *)


Lemma shoutGreeting_correct : shoutGreeting "ignored" = "Hello, ADMIN!".
Proof. reflexivity. Qed.




(* Writer monad example: computing GCD with logging *)

Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Program.Wf.
Require Import Lia.
Require Import Coq.Strings.Ascii.


Open Scope string_scope.

Definition nat_to_string (n : nat) : string :=
  NilEmpty.string_of_uint (Nat.to_uint n).

Definition newline : string := String (ascii_of_nat 10) EmptyString.

Program Fixpoint gcd_writer (a b : nat) {measure b} : Writer nat :=
  match b with
  | 0 =>
      writer_bind (tell ("Finished with " ++ nat_to_string a ++ newline))
                  (fun _ => writer_return a)
  | S b' =>
      writer_bind
        (tell (nat_to_string a ++ " mod " ++ nat_to_string b ++ " = " ++ nat_to_string (a mod b) ++ newline))
        (fun _ => gcd_writer b (a mod b))
  end.
Next Obligation.
  (* Prove a mod b < b *)
  apply Nat.mod_upper_bound. lia.
Qed.

Definition exampleGCD := gcd_writer 8 3.

Compute exampleGCD.

(* Expected:
   (1, "8 mod 3 = 2
   3 mod 2 = 1
   2 mod 1 = 0
   Finished with 1.")
*)


(*
  In addition to verifying the standard monad laws (left identity, right identity, associativity), many monads 
  define specific operations with useful properties. These laws describe how monad-specific functions like 
  [get], [put], [ask], [throw], or [tell] interact with return, bind or other specific functions.
*)

(* State‐specific interaction laws *)

(* (put s1 >>= fun _ => put s2 = put s2): doing two puts in a row, the second wins *)
Lemma put_put :
  forall (S : Type) (s1 s2 : S),
    state_bind (state_put (S:=S) s1) (fun _ => state_put s2)
    = state_put s2.
Proof.
  intros; unfold state_bind, state_put; simpl; reflexivity.
Qed.

(* (put s >>= fun _ => get = put s >>= fun _ => return s): writing then reading the state returns that state *)
Lemma put_get_return :
  forall (S : Type) (s : S),
    state_bind (state_put s) (fun _ => state_get (S:=S))
     = state_bind (state_put (S:=S) s) (fun _ => state_return (S:=S) s).
Proof.
  intros; unfold state_bind, state_put, state_get, state_return; simpl; reflexivity.
Qed.

(* (get >>= fun s => f s = fun t => f t t): generic get–bind feeds the same state into f twice *)
Lemma get_bind :
  forall (S A : Type) (f : S -> State S A),
    state_bind (state_get (S:=S)) f
    = fun t => f t t.
Proof.
  intros; unfold state_bind, state_get; simpl; reflexivity.
Qed.

(* (put s >>= fun _ => get = put s >>= fun _ => return s): putting then getting equals putting then returning *)
Lemma put_get :
  forall (S : Type) (s : S),
    state_bind (state_put (S:=S) s) (fun _ => state_get (S:=S))
    = state_bind (state_put (S:=S) s) (fun _ => state_return (S:=S) s).
Proof.
  intros; unfold state_bind, state_put, state_get, state_return; simpl; reflexivity.
Qed.

(* (get >>= fun s => put s = return tt): reading then writing the same state is a no-op *)
Lemma get_put :
  forall (S : Type),
    state_bind (state_get (S:=S)) (fun s => state_put s)
    = state_return (S:=S) tt.
Proof.
  intros; unfold state_bind, state_get, state_put, state_return; simpl; reflexivity.
Qed.

(* (get >>= fun _ => get = get): reading twice is the same as reading once *)
Lemma get_get :
  forall (S : Type),
    state_bind (state_get (S:=S)) (fun _ => state_get (S:=S))
    = state_get (S:=S).
Proof.
  intros; unfold state_bind, state_get; simpl; reflexivity.
Qed.




(* Exception‐specific interaction laws *)


(* (catch (Success x) handler = Success x): catching a Success keeps it as a Success *)
Lemma catch_success :
  forall (A : Type) (x : A) (handler : string -> Exception A),
    catch (Success x) handler
  = Success x.
Proof.
  intros. unfold catch. reflexivity.
Qed.

(* (catch (Failure msg) handler = handler msg): catching a Failure runs the handler *)
Lemma catch_failure :
  forall (A : Type) (msg : string) (handler : string -> Exception A),
    catch (Failure msg) handler
  = handler msg.
Proof.
  intros. unfold catch. reflexivity.
Qed.

(* (exception_bind (throw msg) f = throw msg): throwing an error stops further actions *)
Lemma throw_bind :
  forall (A B : Type) (msg : string) (f : A -> Exception B),
    exception_bind (throw msg) f
  = throw msg.
Proof.
  intros. unfold exception_bind, throw. reflexivity.
Qed.

(* (exception_bind (Success x) exception_return = Success x): return keeps success unchanged *)
Lemma bind_return_success :
  forall (A : Type) (x : A),
    exception_bind (Success x) exception_return
  = Success x.
Proof.
  intros. unfold exception_bind, exception_return. reflexivity.
Qed.




(* Reader‐specific interaction laws *)


(* (local f ask = reader_bind ask (fun x => reader_return (f x))): pushing f into ask is same as binding ask and 
    returning f x *)
Lemma local_ask_bind :
  forall (R A : Type) (f : R -> R),
    local f (ask (R:=R))
  = reader_bind (ask (R:=R)) (fun x => reader_return (R:=R) (f x)).
Proof.
  intros. unfold local, reader_bind, reader_return. reflexivity.
Qed.

(* (local f (reader_return x) = reader_return x): pushing f into a constant result does nothing *)
Lemma local_return :
  forall (R A : Type) (f : R -> R) (x : A),
    local f (reader_return (R:=R) x)
  = reader_return (R:=R) x.
Proof.
  intros. unfold local, reader_return. reflexivity.
Qed.

(* (local f (reader_bind m g) = reader_bind (local f m) (fun a => local f (g a))): local distributes over bind *)
Lemma local_bind :
  forall (R A B : Type) (f : R -> R) (m : Reader R A) (g : A -> Reader R B),
    local f (reader_bind m g)
  = reader_bind (local f m) (fun a => local f (g a)).
Proof.
  intros. unfold local, reader_bind. reflexivity.
Qed.

(* (local f (local g m) = local (fun r => g (f r)) m): composition of 2 local functions *)
Lemma local_local :
  forall (R A : Type) (f g : R -> R) (m : Reader R A),
    local f (local g m)
  = local (fun r => g (f r)) (R:=R) m.
Proof.
  intros. unfold local. reflexivity.
Qed.

(* (reader_bind ask reader_return = ask): ask then return gives the environment *)
Lemma ask_return :
  forall (R : Type),
    reader_bind (ask (R:=R)) (fun x => reader_return (R:=R) x)
  = ask (R:=R).
Proof.
  intros. unfold reader_bind, reader_return, ask. reflexivity.
Qed.

(* (reader_bind ask (fun _ => ask) = ask): asking twice is the same as asking once *)
Lemma ask_ask :
  forall (R : Type),
    reader_bind (ask (R:=R)) (fun _ => ask (R:=R))
  = ask (R:=R).
Proof.
  intros. unfold reader_bind, ask. reflexivity.
Qed.

(* (reader_bind ask (fun _ => m) = m): using ask to ignore environment gives m *)
Lemma ask_ignore :
  forall (R A : Type) (m : Reader R A),
    reader_bind (ask (R:=R)) (fun _ => m)
  = m.
Proof.
  intros. unfold reader_bind, ask. reflexivity.
Qed.




(* Writer‐specific interaction laws *)


(* (writer_bind (tell msg) (fun _ => writer_return tt) = tell msg): if a msg is logged then do nothing, the msg will 
  still be in the log *)
Lemma tell_return :
  forall (msg : string),
    writer_bind (tell msg) (fun _ => writer_return tt)
  = tell msg.
Proof.
  intros. unfold writer_bind, tell, writer_return. rewrite string_append_empty_r. reflexivity.
Qed.

(* (writer_bind (tell s1) (fun _ => tell s2) = tell (s1 ++ s2)): two tells records both messages *)
Lemma tell_tell :
  forall (s1 s2 : string),
    writer_bind (tell s1) (fun _ => tell s2)
  = tell (s1 ++ s2).
Proof.
  intros. unfold writer_bind, tell. reflexivity.
Qed.

(* (listen (writer_return x) = ((x, ""), "")): listening to a pure value with no log gives an empty log *)
Lemma listen_return :
  forall (A : Type) (x : A),
    listen (writer_return x)
  = ((x, ""), "").
Proof.
  intros. unfold listen, writer_return. reflexivity.
Qed.

(* (listen (tell msg) = ((tt, msg), msg)): listening to a tell returns that message *)
Lemma listen_tell :
  forall (msg : string),
    listen (tell msg)
  = ((tt, msg), msg).
Proof.
  intros. unfold listen, tell. reflexivity.
Qed.

(* (pass (writer_return (x, f)) = (x, f "")): passing on a pure pair applies f to empty log *)
Lemma pass_return :
  forall (A : Type) (x : A) (f : string -> string),
    pass (writer_return (x, f))
  = (x, f "").
Proof.
  intros. unfold pass, writer_return. simpl. reflexivity.
Qed.






(* The State‐transformer type, parametrized by any base monad M with its own return and bind 
  operations. *)


From Coq Require Import Relations Classes.Equivalence Classes.Morphisms.
Open Scope signature_scope.

Class Monad (M : Type -> Type) : Type := {
  returnM  : forall {A}, A -> M A ;
  bindM : forall {A B}, M A -> (A -> M B) -> M B ;
  eqM   {A} : relation (M A);
}.

Arguments returnM  {M _ A} _.
Arguments bindM {M _ A B} _ _.
Arguments eqM {M _ A} _ _.
Notation "x == y" := (eqM x y) (at level 80).


Class MonadLaws (M : Type -> Type) `{Monad M} := {
    eqM_Equivalence :: forall A, Equivalence (@eqM M _ A);

    monad_left_id {A B} (x : A) (f : A -> M B) :
       bindM (returnM x) f == f x;

    monad_right_id {A} (m : M A) :
       bindM m returnM == m;

    monad_assoc {A B C} (m : M A) (f : A -> M B) (g : B -> M C) :
       bindM (bindM m f) g == bindM m (fun x => bindM (f x) g);

    bindM_Proper {A B} :: Proper (eqM ==> (eq ==> eqM) ==> eqM)
                 (bindM (A:=A) (B:=B))
}.


Definition reader_eq {R} A : relation (Reader R A) :=
  fun m1 m2 => forall r, m1 r = m2 r.

Instance reader_monad R : Monad (Reader R) := {
    returnM A x := reader_return x;
    bindM A B m f := reader_bind m f;
    eqM A x y := reader_eq A x y;
  }.

Instance reader_eq_equiv {R} A : Equivalence (reader_eq (R:=R) A).
Proof. 
  split.
  - unfold Reflexive.
    intro x. unfold reader_eq.
    intros r . reflexivity.
  - unfold Symmetric, reader_eq.
    intros. rewrite H. reflexivity.
  - unfold Transitive, reader_eq.
   intros. rewrite H. apply H0.
Qed.

Program Instance reader_monad_laws R : MonadLaws (Reader R).
Next Obligation.
  unfold reader_eq; intros.
  apply reader_left_identity.
Qed.
Next Obligation.
  unfold reader_eq; intros.
  apply reader_right_identity.
Qed.
Next Obligation.
  unfold reader_eq, reader_bind. reflexivity.
Qed.
Next Obligation.
  intros x1 x2 Hx f1 f2 Hf.
  intros r. unfold reader_bind.
  apply Hf. apply Hx.
Qed.


Definition maybe_eq {A} : relation (Maybe A) :=
  fun x y => x = y.

Instance maybe_monad : Monad Maybe := {
   returnM A x := maybe_return x;
   bindM A B m f := maybe_bind m f;
   eqM A := maybe_eq
}.

Instance maybe_eq_equiv {A : Type} : Equivalence (maybe_eq (A := A)).
Proof.
  split.
  - intros x.
    destruct x as [y |].
    + reflexivity.
    + reflexivity.
  - intros x y H.
    destruct x as [x' |].
    + destruct y as [y' |].
      * rewrite <- H. reflexivity.
      * discriminate H.
    + destruct y as [y' |].
      * discriminate H.
      * reflexivity.
  - intros x y z Hxy Hyz.
    destruct x as [x' |].
    + destruct y as [y' |].
      * destruct z as [z' |].
        -- rewrite Hxy, Hyz. reflexivity.
        -- discriminate Hyz.
      * discriminate Hxy.
    + destruct y as [y' |].
      * discriminate Hxy.
      * destruct z as [z' |].
        -- discriminate Hyz.
        -- reflexivity.
Qed.


Program Instance maybe_monad_laws : MonadLaws Maybe.
Next Obligation.
  unfold maybe_eq. reflexivity.
Qed.
Next Obligation.
  unfold maybe_eq, maybe_bind, maybe_return.
  apply maybe_right_identity.
Qed.
Next Obligation.
  unfold maybe_eq, maybe_bind.
  apply maybe_associativity.
Qed.
Next Obligation.
  intros m1 m2 Hm f1 f2 Hf.
  unfold maybe_eq, maybe_bind.
  destruct m1 as [x1|], m2 as [x2|]; simpl; try contradiction.
  - inversion Hm.
    apply Hf. reflexivity.
  - discriminate Hm.
  - discriminate Hm.
  - reflexivity. 
Qed.



Definition exception_eq {A} : relation (Exception A) :=
  fun x y => x = y.

Instance exception_monad : Monad Exception := {
  returnM A x := exception_return x;
  bindM A B m f := exception_bind m f;
  eqM A := exception_eq
}.

Instance exception_eq_equiv {A} : Equivalence (exception_eq (A:=A)).
Proof.
  split.
  - intros x.
    destruct x as [a | msg].
    + reflexivity.
    + reflexivity.
  - intros x y H.
    destruct x as [a1 | msg1], y as [a2 | msg2].
    + destruct H. reflexivity.
    + discriminate H.
    + discriminate H.
    + destruct H. reflexivity.
  - intros x y z Hxy Hyz.
    destruct x as [a1 | msg1], y as [a2 | msg2], z as [a3 | msg3].
    + destruct Hxy, Hyz. reflexivity.
    + discriminate Hyz.
    + discriminate Hyz.
    + discriminate Hxy.
    + discriminate Hxy.
    + destruct Hxy, Hyz. reflexivity.
    + discriminate.
    + destruct Hxy, Hyz. reflexivity.
Qed.

Program Instance exception_monad_laws : MonadLaws Exception.
Next Obligation.
  unfold exception_eq.
  apply exception_left_identity.
Qed.
Next Obligation.
  unfold exception_eq, exception_bind, exception_return.
  apply exception_right_identity.
Qed.
Next Obligation.
  unfold exception_eq, exception_bind.
  apply exception_associativity.
Qed.
Next Obligation.
  intros m1 m2 Hm f1 f2 Hf.
  unfold exception_eq, exception_bind.
  destruct m1 as [x1|e1], m2 as [x2|e2].
  - inversion Hm.
    apply Hf. reflexivity.    
  - discriminate.
  - discriminate.
  - inversion Hm. reflexivity.
Qed.



Definition state_eq {S A} : relation (State S A) :=
  fun m1 m2 => forall s, m1 s = m2 s.

Instance state_monad (S : Type) : Monad (State S) := {
  returnM A x := state_return x;
  bindM A B m f := state_bind m f;
  eqM A m1 m2 := state_eq m1 m2
}.

Instance state_eq_equiv {S A} : Equivalence (state_eq (S:=S) (A:=A)).
Proof.
  split.
  - unfold Reflexive, state_eq. reflexivity.
  - unfold Symmetric, state_eq. intros. rewrite <- H. reflexivity.
  - unfold Transitive, state_eq. intros. rewrite <- H0, H. reflexivity.
Qed.


Program Instance state_monad_laws (S : Type) : MonadLaws (State S).
Next Obligation.
  unfold state_eq, state_bind, state_return.
  intros. reflexivity.
Qed.
Next Obligation.
  unfold state_eq, state_bind, state_return.
  intros s. apply state_right_identity.
Qed.
Next Obligation.
  unfold state_eq, state_bind.
  intros s. apply state_associativity.
Qed.
Next Obligation.
  intros m1 m2 Hm f1 f2 Hf s.
  unfold state_eq, state_bind.
  rewrite Hm.
  destruct (m2 s) as [a s'].
  apply Hf.
  reflexivity.
Qed.



Definition identity_eq {A} : relation (Identity A) := fun x y => x = y.

Instance identity_monad : Monad Identity := {
  returnM A x := identity_return x;
  bindM A B m f := identity_bind m f;
  eqM A := identity_eq
}.

Instance identity_eq_equiv {A} : Equivalence (identity_eq (A:=A)).
Proof.
  split.
  - unfold Reflexive, identity_eq. reflexivity.
  - unfold Symmetric, identity_eq. intros. rewrite <- H. reflexivity.
  - unfold Transitive, identity_eq. intros. rewrite H, H0. reflexivity.
Qed.

Program Instance identity_monad_laws : MonadLaws Identity.
Next Obligation.
  unfold identity_eq, identity_bind, identity_return.
  reflexivity.
Qed.
Next Obligation.
  unfold identity_eq, identity_bind, identity_return.
  reflexivity.
Qed.
Next Obligation.
  unfold identity_eq, identity_bind.
  reflexivity.
Qed.
Next Obligation.
  intros m1 m2 Hm f1 f2 Hf.
  unfold identity_bind, identity_eq.
  rewrite Hm.
  apply Hf. reflexivity.
Qed.



Definition writer_eq {A} : relation (Writer A) := fun x y => x = y.

Instance writer_monad : Monad Writer := {
  returnM A x := writer_return x;
  bindM A B m f := writer_bind m f;
  eqM A := writer_eq
}.

Instance writer_eq_equiv {A} : Equivalence (writer_eq (A:=A)).
Proof.
  split.
  - unfold Reflexive, writer_eq.  intros x. reflexivity.
  - unfold Symmetric, writer_eq. intros x y H. rewrite H. reflexivity.
  - unfold Transitive, writer_eq. intros x y z H H'. rewrite H, H'. reflexivity.
Qed.

Program Instance writer_monad_laws : MonadLaws Writer.
Next Obligation.
  unfold writer_eq, writer_bind, writer_return.
  destruct (f x) as [b log]. reflexivity.
Qed.
Next Obligation.
  unfold writer_eq, writer_bind, writer_return.
  destruct m as [a log].
  apply f_equal.
  apply string_append_empty_r.
Qed.
Next Obligation.
  unfold writer_eq, writer_bind.
  intros.
  destruct m as [a log1].
  destruct (f a) as [b log2].
  destruct (g b) as [c log3].
  rewrite string_append_assoc.
  reflexivity.
Qed.
Next Obligation.
  intros m1 m2 Hm f1 f2 Hf.
  unfold writer_bind, writer_eq.
  destruct m1 as [a1 log1], m2 as [a2 log2].
  destruct (f1 a1) as [b1 l1], (f2 a2) as [b2 l2].
  Admitted.




Definition StateT (S : Type) (M : Type -> Type) `{Monad M} (A : Type) : Type :=
  S -> M (prod A S).


Definition stateT_return {S M A} `{Monad M} (x : A) : StateT S M A :=
  fun s => returnM (x, s).

Definition stateT_bind {S M A B} {MonadM : Monad M} (m : StateT S M A) (k : A -> StateT S M B) : StateT S M B :=
  fun s => bindM (m s) (fun (p : A * S) => let (a, s') := p in k a s').


Definition statet_eq {S} M `{Monad M}  A : relation (StateT S M A) :=
  fun m1 m2 => forall s, m1 s == m2 s.

Instance stateT_monad S M `{Monad M} : Monad (StateT S M) :=
  {
    returnM A x := stateT_return x;
    bindM A B m f := stateT_bind m f;
    eqM A x y := statet_eq M A x y;
  }.


Instance statet_eq_equiv {S} M `{Monad M} `{MonadLaws M} A :
  Equivalence (statet_eq (S:=S) M A).
Proof.
  split.
  - unfold Reflexive, statet_eq. reflexivity.
  - unfold Symmetric, state_eq. intros m1 m2 H2 s. admit.
  - unfold Transitive, state_eq. intros m1 m2 m3 H2 H3 s. rewrite H12.
Qed.

Program Instance stateT_monad_laws S M `{Monad M} `{MonadLaws M} :
  MonadLaws (StateT S M).

Obligation 2.
unfold statet_eq.
unfold stateT_bind, stateT_return.
intros r.
transitivity (bindM (m r) returnM).
- f_equiv. intros [p1 p2] [p1' p2'].
  intro Heq. rewrite Heq. reflexivity.
- apply monad_right_id.
Qed.


(*rewrite monad_left_id.*)











Definition liftT {S M A} `{Monad M} (ma : M A) : StateT S M A :=
  fun s => bindM ma (fun a => returnM (a, s)).

Definition getT {S M} `{Monad M} : StateT S M S :=
  fun s => returnM (s, s).

Definition putT {S M} `{Monad M} (s' : S) : StateT S M unit :=
  fun _ => returnM (tt, s').



(* Monad laws for StateT Monad Transformer *)

(* Left Identity *)
Lemma stateT_left_identity :
  forall (S : Type) (M : Type -> Type) (MonadM : Monad M)
         (A B : Type) (x : A) (f : A -> StateT S M B) (s : S),
    stateT_bind (stateT_return x) f s = f x s.
Proof.
  intros. unfold stateT_bind, stateT_return.
  simpl.
 Admitted.


(* Right Identity *)
Lemma stateT_right_identity :
  forall (S : Type) (M : Type -> Type) (MonadM : Monad M)
         (A : Type) (m : StateT S M A),
    stateT_bind m stateT_return = m.
Proof.
Admitted.

(* Associativity *)
Lemma stateT_associativity :
  forall (S : Type) (M : Type -> Type) (MonadM : Monad M)
         (A B C : Type)
         (m : StateT S M A)
         (f : A -> StateT S M B)
         (g : B -> StateT S M C),
    stateT_bind (stateT_bind m f) g =
    stateT_bind m (fun x => stateT_bind (f x) g).
Proof.
Admitted. 


(* liftT (returnM x) s = returnM (x, s) 
Lemma StateT_lift_return
*)

(* liftT (m >>= k) s = (liftT m >>= fun x => liftT (k x)) s
Lemma StateT_lift_bind :
*)