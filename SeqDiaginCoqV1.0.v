(* Copyright (c) 2012, Department of Computer Science and Engineering
 * East China Normal University, Shanghai, China.
 * All rights reserved.
 * Author: Dou Liang, Zuo Ying
 * Email: ldou@cs.ecnu.edu.cn; zyzuoying@gmail.com
 * Description: Toward Mechanized Semantics of UML Sequence
     Diagrams and Refinement Relation
*)
Require Export String Bool ListSet List Arith.
Open Scope type_scope.
(*=========Definition of Semantic Model of Sequence Diagrams============*)
Inductive kind : Set := | Send : kind | Receive : kind.
Notation "!" := Send (at level 40).
Notation "?" := Receive (at level 40).
Definition signal := string.
Definition lifeline := string.
(*An event is defined as a signal send between two lifelines with kind *) 
Definition event := kind * signal * lifeline * lifeline.
(* The definition specifies the syntax of condition*)
Inductive id : Set := Id : nat -> id.
Inductive cnd : Type := | Bvar : id -> cnd | Btrue : cnd 
| Bfalse : cnd | Bnot : cnd -> cnd | Band : cnd -> cnd -> cnd 
| Bor : cnd -> cnd -> cnd | Bimp : cnd -> cnd -> cnd.
Inductive tk : Set := | ev : event -> tk | cd : cnd -> tk.
(*A trace is a list of events and conditions*)
Definition trace := list tk.
(*A model is a set of acceptable traces*)
Definition model := trace -> Prop.



(*===========Equality Judgement============*)
Definition singal_dec : forall s1 s2:signal, {s1 = s2} + {s1 <> s2}.
    exact string_dec.
Defined.
Definition lifeline_dec : forall l1 l2:lifeline, {l1 = l2} + {l1 <> l2}.
    repeat decide equality.
Defined.
Definition kind_dec : forall k1 k2:kind, {k1 = k2} + {k1 <> k2}.
   repeat decide equality. 
Defined.
Definition event_dec:forall e1 e2:event,  {e1 = e2} + {e1 <> e2}.
   repeat decide equality. 
Defined.
Definition trace_dec:forall t1 t2:trace,  {t1 = t2} + {t1 <> t2}.
   repeat decide equality.
Defined.

(*==========Syntax of Sequence Diagrams==================*)
Inductive seqDiag : Set := | Dtau : seqDiag 
| De : event -> seqDiag | Dpar : seqDiag -> seqDiag -> seqDiag
| Dalt : cnd -> seqDiag -> seqDiag -> seqDiag 
| Dopt : cnd -> seqDiag -> seqDiag
| Dstrict : seqDiag -> seqDiag -> seqDiag
| Dloop : nat -> cnd -> seqDiag -> seqDiag.

(*==========Auxiliary Functions ==================*)
Definition state := id -> bool.
(*Evaluate a condition and reduce it to boolean value*)
Fixpoint beval (st : state)(c : cnd) : bool :=
  match c with 
  | Bvar i => st i
  | Btrue => true
  | Bfalse => false
  | Bnot b1 => negb (beval st b1)
  | Band b1 b2 => andb (beval st b1) (beval st b2)
  | Bor b1 b2 => orb (beval st b1) (beval st b2)
  | Bimp b1 b2 => orb (negb (beval st b1)) (beval st b2) (*translate [P->Q] into [(not P)\/Q]*)
  end.

Reserved Notation "x // y" (at level 5).
Inductive interleave : trace -> trace -> trace -> Prop :=
| Nrule : nil // nil nil
| Lrule : forall x v u t, v // u t -> (x :: v) // u (x :: t)
| Rrule : forall v y u t, v // u t ->  v //(y :: u) (y :: t)
where "x // y" := (interleave x y).

(*==========Definition of Denotational Functions==========*)
Reserved Notation "x => y" (at level 70).
Inductive interp : seqDiag -> model :=
| Int_Dtau : Dtau => nil
| Int_De : forall e, De e => (ev e) :: nil
| Int_Dopt1 : forall sd w c, sd => w -> Dopt c sd => (cd c)::w
| Int_Dopt2 : forall sd c, Dopt c sd => nil 
| Int_Dpar : forall sd1 sd2 w1 w2 w ,
    sd1 => w1 -> sd2 => w2 -> w1 // w2 w ->Dpar sd1 sd2 => w 
| Int_Dalt1 : forall sd1 sd2 w c, sd1 => w -> 
    Dalt c sd1 sd2 => (cd c) :: w
| Int_Dalt2 : forall sd1 sd2 w c, sd2 => w -> 
    Dalt c sd1 sd2 => (cd (Bnot c)) :: w
| Int_Dstrict : forall sd1 sd2 w1 w2, sd1 => w1 -> sd2 => w2 -> 
    Dstrict sd1 sd2 => w1 ++ w2
| Int_DloopNil : forall sd c, Dloop 0 c sd => nil
| Int_Dloop : forall sd w w' c n, sd => w -> Dloop n c sd => w' -> 
    Dloop (S n) c sd => w' ++ ((cd c) :: w)
where "x => y" := (interp x y).

(*==========Definition of Context==========*)
Definition context : Set := seqDiag -> seqDiag.
Inductive iscx : context -> Prop :=
| Ich : iscx (fun x => x)
| Icpl : forall C s, iscx C -> iscx (fun x => Dpar (C x) s)
| Icpr : forall s C, iscx C -> iscx (fun x => Dpar s (C x))
| Ico : forall C c, iscx C -> iscx (fun x => Dopt c (C x))
| Ical : forall C c s, iscx C -> iscx (fun x => Dalt c (C x) s)
| Icar : forall C c s, iscx C -> iscx (fun x => Dalt c s (C x))
| Icsl : forall C s, iscx C -> iscx (fun x => Dstrict (C x) s)
| Icsr : forall s C, iscx C -> iscx (fun x => Dstrict s (C x))
| Iclp : forall C c n, iscx C -> iscx (fun x => Dloop n c (C x)).

(*==========Properties of Trace Semantics==============**)
(*Trivial lemmas for interleave*)
Lemma trivial_int1 : forall l1 l2, l1 // l2 (l1++l2).
Proof.
  intros l1 l2; induction l1;
  [induction l2; constructor; auto|constructor; auto].
Qed.
Hint Resolve trivial_int1.

Lemma trivial_int2 : forall z, nil // z z.
Proof.
  induction z. apply Nrule. apply Rrule; trivial.
Qed.
Hint Resolve trivial_int2.

Lemma trivial_int3 : forall z, z // nil z.
Proof.
  induction z. apply Nrule. apply Lrule; trivial.
Qed.
Hint Resolve trivial_int3.

Lemma trivial_int4 : forall b c, nil // b c -> b = c.
Proof.
  induction b. intros c H. inversion H. auto.
  intros c H. inversion H. subst. apply IHb in H4. subst. auto.
Qed.
Hint Resolve trivial_int4.

Lemma trivial_int5 : forall a b c, a // b c ->  b // a c.
Proof.
  intros a b c H. induction H. auto. now constructor. 
  now constructor.
Qed.
Hint Resolve trivial_int5.

(*Lemma 1*)
Lemma trace_exist : forall (sd : seqDiag), exists t, sd => t.
Proof.
  induction sd.
  (*TAU*)
  exists nil; constructor.
  (*EVENT*)
  exists (ev e :: nil); constructor.
  (*PAR*)
  destruct IHsd1; destruct IHsd2.
  exists (x ++ x0).
  apply Int_Dpar with(w1 := x)(w2 := x0) ; try assumption. auto.
  (*ALT*)  
  destruct IHsd1; destruct IHsd2.
  exists (cd c :: x);  now constructor.
  (*OPT*)
  exists (nil);  constructor.
  (*STRICT*)
  destruct IHsd1; destruct IHsd2.
  exists (x ++ x0); now constructor.
  (*LOOP*)
  induction n.
  exists nil; constructor.
  destruct IHsd; destruct IHn; exists (x0 ++ (cd c) :: x); now constructor.
Qed.

(*Trivial lemmas for union events*)
Lemma trivial_union_event_nil : forall l1 l2, set_union event_dec l1 l2 = nil ->
  l1 = nil /\l2 = nil.
Proof.
 intros l1 l2 H.
 induction l1;destruct l2;simpl in *.
 split;auto. split;auto. 
 contradict H. apply set_add_not_empty.
 inversion H.  contradict H. apply set_add_not_empty.
Qed.

(*Lemma 2*)
Lemma context_insensitive: forall d1 d2 C , 
  (forall t1, d1 => t1 <->  d2 => t1) ->  iscx C ->
  (forall t2, (C d1) => t2 <-> (C d2) => t2).
Proof.
 intros d1 d2 C H1 H2.
 revert H1.
 induction H2;intros.
(*Self*)
 auto.
(*Lpar*)
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. destruct (H3 w1). subst.  apply H9 in H5.
 apply Int_Dpar with (sd1 := (C d2))(sd2 := s)(w1 := w1)(w2 := w2); assumption.
 intro H4.  inversion H4. destruct (H3 w1). subst.  apply H10 in H5.
 apply Int_Dpar with (sd1 := (C d1))(sd2 := s)(w1 := w1)(w2 := w2); assumption.
(*Rpar*)
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. destruct (H3 w2). subst.  apply H9 in H6.
 apply Int_Dpar with (sd1 := s)(sd2 := (C d2))(w1 := w1)(w2 := w2); assumption.
 intro H4.  inversion H4. destruct (H3 w2). subst.  apply H10 in H6.
 apply Int_Dpar with (sd1 := s)(sd2 := (C d1))(w1 := w1)(w2 := w2); assumption.
(*Opt*) 
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. destruct (H3 w). subst. 
 apply H7 in H6. constructor. assumption. constructor.
 intro H4.  inversion H4. destruct (H3 w). subst.
 apply H8 in H6. constructor. assumption. constructor.
 (*Lalt*)
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. destruct (H3 w). subst.
 apply H8 in H7. constructor. assumption. constructor. assumption.
 intro H4.  inversion H4. destruct (H3 w).
 apply H9 in H7. constructor. assumption. constructor. assumption.
(*Ralt*)
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. constructor. assumption.
 destruct (H3 w). subst.
 apply H8 in H7. constructor. assumption. 
 intro H4.  inversion H4. constructor. assumption.
 destruct (H3 w).
 apply H9 in H7. constructor. assumption. 
 (*Lstrict*)
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. destruct (H3 w1). subst.
 apply H8 in H5. constructor. assumption. assumption.
 intro H4.  inversion H4. destruct (H3 w1).
 apply H9 in H5. constructor. assumption. assumption.
(*Rstrict*)
 remember (IHiscx H1) as H3.  
 split.
 intro H4.  inversion H4. destruct (H3 w2). subst.
 apply H8 in H7. constructor. assumption. assumption.
 intro H4.  inversion H4. destruct (H3 w2).
 apply H9 in H7. constructor. assumption. assumption.
(*LOOP*)
 revert H1 t2.
 induction n.
  split;try (intro H;inversion H; subst; constructor;auto).
  intros.
  remember (IHiscx H1) as H3.   split.
 intro H4.   inversion H4. constructor. destruct (H3 w). 
 apply H9 in H7.  assumption.
 remember (IHn H1) as H9.
 destruct (H9 w'). apply H10 in H8. assumption.
 intro H4.   inversion H4. constructor. destruct (H3 w). 
 apply H10 in H7.  assumption.
 remember (IHn H1) as H9.
 destruct (H9 w'). apply H11 in H8. assumption.
Qed. 

(*==========Properties of Refinement==============**)
Require Import Relations.
(*Definition 1*)
Inductive simulate (st : state) : trace -> trace -> Prop :=
| Sba : simulate st nil nil
| Scd : forall c1 c2 t t', beval st (Bimp c2 c1) = true -> 
    simulate st t t' -> simulate st ((cd c1) :: t) ((cd c2) :: t')
| Sev : forall t t' e , simulate st t t' -> 
    simulate st ((ev e) :: t) ((ev e) :: t')
| Sadd : forall e t t', simulate st t t' -> simulate st t ((ev e) :: t').

(*trivial lemmas for Lemma 3*)
Lemma bimp_refl : forall c st, beval st (Bimp c c) = true .
Proof.
 intros c0 st. simpl. destruct (beval st c0); auto.
Qed.

Lemma beval_trans : forall cnd1 cnd2 cnd3 st, beval st (Bimp cnd1 cnd2) = true 
         -> beval st (Bimp cnd2 cnd3) = true -> beval st (Bimp cnd1 cnd3) = true.
Proof.
   simpl; intros.
   destruct (negb (beval st cnd1)); simpl in *; auto.
   destruct (beval st cnd2); simpl in *; auto.
   discriminate.
Qed.

(*Lemma 3 part1*)
Lemma simu_refl : forall st : state, reflexive _ (simulate st).
Proof.
  intro st.  unfold reflexive. intro x. 
  induction x. apply Sba. induction a.
  apply Sev. assumption. apply Scd. apply bimp_refl. assumption. 
Qed.
Hint Resolve simu_refl.

(*Lemma 3 part2*)
Lemma simu_trans : (forall st : state, transitive _ (simulate st)).
Proof.
  intro st. unfold transitive. intros x y z H .
  revert z.
  induction H; intros; auto.
 (*case 1*)
   assert (forall c, beval st (Bimp c c2) = true -> beval st (Bimp c c1) = true). 
    clear - H; intros; simpl in *.
    destruct (beval st c); simpl in *; auto.
    rewrite H0 in H; simpl in *; auto.
   clear - IHsimulate H1 H2.
   remember (cd c2 :: t') as X.
   revert c2 t' HeqX IHsimulate H2.
   induction H1; intros; inversion HeqX; clear HeqX; subst.
    clear - H H1 H2 IHsimulate0.
    now constructor; auto.
   constructor.
   now eapply IHsimulate; eauto.
(*case 2*)
  inversion H0; clear H0; subst.
   now constructor; auto.
  constructor; auto.
  remember (ev e :: t') as X.
  revert e t' HeqX IHsimulate H.
  induction H1; intros; inversion HeqX; clear HeqX; subst.
   clear - H H1 IHsimulate0.
   now constructor; auto.
  constructor 4.
  now eapply IHsimulate; eauto.
 remember (ev e :: t') as X.
 revert e t' HeqX IHsimulate H.
 induction H0; intros; inversion HeqX; clear HeqX; subst.
  clear - H0 IHsimulate0.
  now constructor; auto.
 now econstructor; eapply IHsimulate.
Qed.

(*Definition 2*)
Definition refine (st : state)(m1 m2 : model) : Prop :=
  forall t1 : trace, m1 t1 -> 
  exists t2 : trace, m2 t2 /\ simulate st t1 t2.

(*Auxiliary lemma for theorem 1 *)
Lemma trivial_bimp st c : beval st (Bimp c c) = true.
Proof.
  simpl. induction (beval st c); reflexivity.
Qed.
Hint Resolve trivial_bimp. 

Lemma simu_exist : forall st a b z az, simulate st a b -> 
  a // z az -> exists bz, b // z bz /\ simulate st az bz.
Proof.
intros st a b z az H1 H2.
revert b H1.
(* Do induction on the interleaving of a and z *)
induction H2; intuition.
 (* 1: a and z are both nil
        b simulates a, so it simulates az since both are nil *)
  exists b; intuition.
 (* 2: a = (x :: v) and az = (x :: t) for some (v // z t) (where z = u)
    we know that b simulates a, so we to want to pick
    the initial segment of b which simulates x, using induction
    on the simulation of a by b *)
 set (a := (x :: v)). (* Make sure coq doesn't forget the structure of a *)
 assert (a = x :: v) by reflexivity.
 rewrite <- H in H1.
 induction H1; inversion H; subst.

  (* A: simulation between conditions in a and b *)
  destruct (IHinterleave _ H1).
  exists (cd c2 :: x); intuition.
   apply Lrule; trivial.
   apply Scd; trivial.

 (* B: simulation between events in a and b *)
 destruct (IHinterleave _ H1).
 exists (ev e :: x); intuition.
   apply Lrule; trivial.
   apply Sev; trivial.

 (* C: b has an extra event: we need the inductive hypothesis *)
 intuition.
 destruct H.
 exists (ev e :: x0).
 intuition.
  apply Lrule; trivial.
  apply Sadd; trivial.

 (* 3: b = (y :: u) and az = (y :: t) for some (a // u t) (where a = v)
    we simulate the z event first *)
 destruct (IHinterleave _ H1).
 exists (y :: x).
 intuition.
 apply Rrule; trivial.
 induction y.
  apply Sev; trivial.
  apply Scd; trivial.
Qed.

(*Theorem 1 part1*)
Theorem refine_refl : forall st : state, reflexive _ (refine st).
Proof.
  intro st.
  unfold reflexive. unfold refine.
  intros x t2 H .
  exists t2. split. assumption.  apply simu_refl.
Qed.

(*Theorem 1 part2*)
Theorem refine_trans : forall st : state, transitive _ (refine st).
Proof.
 intro st. unfold transitive.
 intros x y z.
 unfold refine.   
 intros H1 H2 t2 H.
 destruct (H1 _ H) as [t1 [Ht2 F]]; clear H1 H.
 destruct (H2 _ Ht2) as [t3 [Ht3 G]]; clear H2 Ht2.
 exists t3; split; auto.
 apply (simu_trans st t2 t1 t3);assumption.
Qed.

(*Auxiliary  lemmas for simulation*)
Lemma simu_nil : forall st x, simulate st x nil -> x=nil.
Proof.
  intros st x H. inversion H. auto.
Qed.
  
Lemma simu_app : forall st t1 t2 t3 t4, simulate st t1 t2 -> simulate st t3 t4
                 -> simulate st (t1 ++ t3) (t2 ++ t4).
Proof.
  intros st t1 t2 t3 t4 H H1.
  induction H;try (simpl; constructor; apply IHsimulate; assumption).
  rewrite app_nil_l; rewrite app_nil_l; assumption.
  simpl; constructor. assumption. apply IHsimulate; assumption.
Qed.

(*Theorem 1 part3*)
Theorem refine_context_insensitive : forall (st : state) (d1 : seqDiag)
(d2 : seqDiag)(C : context), iscx C -> refine st (interp d1) (interp d2) 
  -> refine st (interp (C d1)) (interp (C d2)).
Proof.
 intros st d1 d2 C H H1.
 unfold refine in *.
 induction H.
(*Self*)
 auto.
(*Lpar*)
 clear H H1.
 intros gt1 H.
 inversion H. clear H. subst.
 destruct (IHiscx _ H2). destruct H.
 apply simu_exist with (z := w2)(az := gt1)  in H0.
 destruct H0.
 exists x0. 
 destruct H0.
 split; auto.
 econstructor; eauto. auto. 
 (*Rpar*)
 clear H H1.
 intros gt1 H.
 inversion H. clear H. subst.
 destruct (IHiscx _ H3). destruct H.
 apply simu_exist with (z := w1)(az := gt1)  in H0.
 destruct H0.
 exists x0.
 destruct H0.
 split; auto.
 econstructor; eauto. auto.
 (*OPT*)
 clear H H1.
 intros gt1 H.
 inversion H. clear H. subst.
 destruct (IHiscx _ H3).
 exists (cd c :: x).
 destruct H.
 split; constructor;auto.
 exists  nil.
 split. apply Int_Dopt2. apply simu_refl.
 (*LALT*)
 clear H H1.
 intros gt1 H.
 inversion H; clear H; subst.
 destruct (IHiscx _ H4);destruct H.
 exists (cd c :: x).
 split; constructor;auto.
 exists (cd (Bnot c) :: w).
 split;constructor;auto. apply simu_refl. 
 (*Ralt*)
 clear H H1.
 intros gt1 H.
 inversion H; clear H; subst.
 exists (cd c :: w).
 split;constructor;auto. apply simu_refl.
 destruct (IHiscx _ H4);destruct H.
 exists (cd (Bnot c) :: x).
 split; constructor;auto.
 (*Lstrict*)
 clear H H1.
 intros gt1 H.
 inversion H; clear H; subst.
 destruct (IHiscx _ H2);destruct H.
 exists (x ++ w2).
 split. constructor;auto.
 apply simu_app. assumption. apply simu_refl.
 (*Rstrict*)
 clear H H1.
 intros gt1 H.
 inversion H; clear H; subst.
 destruct (IHiscx _ H4);destruct H.
 exists (w1 ++ x).
 split. constructor;auto.
 apply simu_app. apply simu_refl. assumption. 
 (*Loop*)
 clear H H1.  induction n;subst.
 intros t H. inversion H. subst.
 exists  nil. split. constructor.
 apply simu_refl.
 intros gt1 H.
 inversion H; clear H; subst.
 apply IHn in H5. destruct H5. destruct H.
 destruct (IHiscx _ H4);destruct H1.
 exists (x ++ cd c :: x0).
 split. apply Int_Dloop;assumption. 
 apply simu_app. assumption.  constructor. auto. assumption. 
Qed.

(*Example 1*)
Open Scope string_scope.
Definition o1 : lifeline := "o1".
Definition o2 : lifeline := "o2".
Definition m : signal := "m".
Definition n : signal := "n".
Definition f1 : event := (!,m,o1,o2).
Definition f2 : event := (?,m,o1,o2).
Definition f3 : event := (!,n,o1,o2).
Definition f4 : event := (?,n,o1,o2).
Definition D1 : seqDiag := Dstrict (De f1) (De f2).
Definition D2 : seqDiag := Dstrict (De f3) (De f4).
Definition c : cnd := Band (Bvar (Id 2)) (Bvar (Id 3)).
Definition strictD1D2 : seqDiag := Dstrict D1 D2.
Definition parD1D2 : seqDiag := Dpar D1 D2.
Definition optD1 : seqDiag := Dopt c D1.
Definition altD1D2 : seqDiag := Dalt c D1 D2.
Definition loop2D1 : seqDiag := Dloop 2 c D1.

Open Scope list_scope.
Example interp_D1 : (interp D1) ((ev f1) :: (ev f2) :: nil).
Proof.
  assert ((ev f1 :: ev f2 ::nil )=((ev f1) :: nil) ++ ((ev f2) :: nil)).
  auto. rewrite H. unfold D1. econstructor; constructor.
Qed.
Example interp_D2 : (interp D2) ((ev f3) :: (ev f4) :: nil).
Proof.
  assert ((ev f3 :: ev f4 :: nil )=((ev f3) :: nil) ++ ((ev f4) :: nil)).
  auto. rewrite H. unfold D1. econstructor; constructor.
Qed.
Example interp_optD1_1 : (interp optD1) ((cd c) :: (ev f1) :: (ev f2) :: nil).
Proof. econstructor. apply interp_D1. Qed.

Example interp_optD1_2: (interp optD1) (nil).
Proof. econstructor. Qed.

Example interp_altD1D2_1 : (interp altD1D2) ((cd c) :: (ev f1) :: (ev f2) :: nil).
Proof. econstructor. apply interp_D1. Qed.

Example interp_altD1D2_2 : (interp altD1D2) ((cd (Bnot c)) :: (ev f3) :: (ev f4) :: nil).
Proof. econstructor. apply interp_D2. Qed.

Example interp_loop2D1 : (interp loop2D1) ((cd c) :: (ev f1) :: (ev f2) ::(cd c) :: (ev f1) :: (ev f2):: nil).
Proof. 
  assert (((cd c) :: (ev f1) :: (ev f2) ::(cd c) :: (ev f1) :: (ev f2):: nil)=
           (((cd c) :: (ev f1) :: (ev f2) :: nil) ++ ((cd c) :: (ev f1) :: (ev f2):: nil))).
  auto. rewrite H. econstructor. 
  apply interp_D1. 
  assert (( cd c :: ev f1 :: ev f2 :: nil)= nil ++ ( cd c :: ev f1 :: ev f2 :: nil)).
  auto. rewrite H0. econstructor. 
  apply interp_D1. constructor.
Qed.
 
Example interp_strictD1D2: interp strictD1D2 ((ev f1)::(ev f2)::(ev f3)::(ev f4)::nil).
Proof.
  assert (((ev f1) :: (ev f2) :: (ev f3) :: (ev f4) :: nil)= ((ev f1) :: (ev f2) :: nil) ++ ((ev f3) :: (ev f4) :: nil)).
  auto. rewrite H. unfold strictD1D2. econstructor. apply interp_D1. apply interp_D2.
Qed.
Hint Resolve interp_strictD1D2. 

Example interp_parD1D2_1: interp parD1D2 ((ev f1)::(ev f2)::(ev f3)::(ev f4)::nil).
Proof.
 unfold parD1D2.
 econstructor. apply interp_D1. apply interp_D2.
 repeat econstructor.
Qed.

Example interp_parD1D2_2: interp parD1D2 ((ev f1)::(ev f3)::(ev f2)::(ev f4)::nil).
Proof.
 unfold parD1D2.
 econstructor. apply interp_D1. apply interp_D2.
 repeat econstructor.
Qed.

Example interp_parD1D2_3: interp parD1D2 ((ev f1)::(ev f3)::(ev f4)::(ev f2)::nil).
Proof.
 unfold parD1D2.
 econstructor. apply interp_D1. apply interp_D2.
 repeat econstructor.
Qed.

Example interp_parD1D2_4: interp parD1D2 ((ev f3)::(ev f4)::(ev f1)::(ev f2)::nil).
Proof.
 unfold parD1D2.
 econstructor. apply interp_D1. apply interp_D2.
 repeat econstructor.
Qed.

Example interp_parD1D2_5: interp parD1D2 ((ev f3)::(ev f1)::(ev f4)::(ev f2)::nil).
Proof.
 unfold parD1D2.
 econstructor. apply interp_D1. apply interp_D2.
 repeat econstructor.
Qed.

Example interp_parD1D2_6: interp parD1D2 ((ev f3)::(ev f1)::(ev f2)::(ev f4)::nil).
Proof.
 unfold parD1D2.
 econstructor. apply interp_D1. apply interp_D2.
 repeat econstructor.
Qed.

Lemma refineTest: forall st : state, 
      refine st (interp D1) (interp strictD1D2).
Proof.
 intro st; unfold refine; intros t1 H1.
 inversion H1; inversion H2;  inversion H4 ; subst. 
 exists ((ev f1)::(ev f2)::(ev f3)::(ev f4)::nil).
 split; eauto; repeat constructor.
Qed.


(*Example 2, written by notation "=>" *)
Open Scope string_scope.

Definition e1 : event := (!,"m1","l1","l2").
Definition e2 : event := (?,"m1","l1","l2").
Definition e3 : event := (!,"m2","l1","l2").
Definition e4 : event := (?,"m2","l1","l2").
Definition e5 : event := (!,"m3","l1","l2").
Definition e6 : event := (?,"m3","l1","l2").
Definition c1 : cnd := Bvar (Id 1).
Definition c2 : cnd := Band (Bvar (Id 1)) (Bvar (Id 2)).
Definition RefineD1 : seqDiag := 
  Dopt c1 (Dstrict (De e1) (De e2)).
Definition RefineD2 : seqDiag := 
  Dstrict 
  (Dstrict (Dstrict (De e3) (De e4)) 
    (Dstrict (De e5) (De e6))) 
  (Dopt c2 (Dstrict (De e1) (De e2))).

Definition D_1 : seqDiag := Dstrict (De e1) (De e2).
Definition D_2 : seqDiag := Dstrict (De e3) (De e4).
Definition D_3 : seqDiag := Dstrict (De e5) (De e6).

Open Scope list_scope.
Example interp_D_1 : D_1 => (ev e1) :: (ev e2) ::nil.
Proof.
 assert ((ev e1 :: ev e2 ::nil )=((ev e1) :: nil) ++ ((ev e2) :: nil)).
 auto. rewrite H.  econstructor; constructor.
Qed.
Hint Resolve interp_D_1.

Example interp_D_2 : D_2 => (ev e3) :: (ev e4) ::nil.
Proof.
 assert ((ev e3 :: ev e4 ::nil )=((ev e3) :: nil) ++ ((ev e4) :: nil)).
 auto. rewrite H.  econstructor; constructor.
Qed.
Hint Resolve interp_D_2.

Example interp_D_3 : D_3 => (ev e5) :: (ev e6) ::nil.
Proof.
 assert ((ev e5 :: ev e6 ::nil )=((ev e5) :: nil) ++ ((ev e6) :: nil)).
 auto. rewrite H.  econstructor; constructor.
Qed.
Hint Resolve interp_D_3.

Example interp_RefineD1_1 : RefineD1 => (cd c1) :: (ev e1) :: (ev e2) :: nil.
Proof.
 econstructor. auto.
Qed.
Hint Resolve interp_RefineD1_1.

Example interp_RefineD2_1 : 
  RefineD2 => (ev e3) :: (ev e4) :: (ev e5) :: (ev e6) :: (cd c2) :: (ev e1) :: (ev e2) ::nil.
Proof.
 assert ( (ev e3) :: (ev e4) :: (ev e5) :: (ev e6) :: (cd c2) :: (ev e1) :: (ev e2) :: nil =
         (( (ev e3) :: (ev e4) :: (ev e5) :: (ev e6) :: nil) ++ (cd c2) :: (ev e1) :: (ev e2) :: nil) ).
 auto. rewrite H. econstructor. 
 assert (ev e3 :: ev e4 :: ev e5 :: ev e6 :: nil =
         (ev e3 :: ev e4 :: nil) ++ (ev e5 :: ev e6 :: nil)).
 auto. rewrite H0. econstructor;auto. econstructor. auto.
Qed.
Hint Resolve interp_RefineD2_1.

Example interp_RefineD2_2 : 
  RefineD2 => (ev e3) :: (ev e4) :: (ev e5) :: (ev e6) ::nil.
Proof.
 assert ((ev e3) :: (ev e4) :: (ev e5) :: (ev e6)  :: nil =
         (((ev e3) :: (ev e4) :: (ev e5) :: (ev e6)  :: nil) ++ nil)).
 auto. rewrite H. econstructor. 
 assert (ev e3 :: ev e4 :: ev e5 :: ev e6 :: nil =
         (ev e3 :: ev e4 :: nil) ++ (ev e5 :: ev e6 :: nil)).
 auto. rewrite H0. econstructor;auto. econstructor.
Qed.
Hint Resolve interp_RefineD2_2.

Example c2_imp_c1: forall st:state, beval st (Bimp c2 c1) = true.
Proof.
 intro st; unfold c1; unfold c2 ;simpl.
 remember (st (Id 1)) as g1.  remember (st (Id 2)) as g2. 
 rewrite negb_andb.
 assert (negb g1 || negb g2 = negb g2 || negb g1) .
 apply orb_comm. rewrite H. rewrite <- orb_assoc. apply orb_true_iff. right.
 rewrite orb_comm. apply orb_negb_r.
Qed.
Hint Resolve c2_imp_c1.

Lemma ref_example : forall st : state ,
   refine st (interp RefineD1) (interp RefineD2).
Proof.
intro st; unfold refine; intros t1 H1.
inversion H1; inversion H3.
inversion H6; inversion H8; subst. 
exists ((ev e3) :: (ev e4) :: (ev e5) :: (ev e6) :: 
  (cd c2) :: (ev e1) :: (ev e2) :: nil).
split; try(eauto; repeat econstructor; auto). 
exists ((ev e3) :: (ev e4) :: (ev e5) :: (ev e6) ::  nil).
split; try(eauto; repeat econstructor; auto). 
Qed.