Require Import Program.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

(** Dialectica as games in normal form *)


(** * Dialectica category *)

Module DSet.

  (** ** Objects *)

  (** We look at Dialectica objects as games in normal form.
    They define a set of strategies, a set of counter-strategies,
    and a criterion for winning strategy profiles. *)

  Record t :=
    {
      strat : Type;
      costrat : Type;
      winning :> strat -> costrat -> Prop;
    }.

  (** Winning strategies *)

  Definition wstrat (α : t) :=
    {u | forall x, α u x}.

  Coercion w_strat {α : t} (u : wstrat α) : strat α :=
    proj1_sig u.


  (** ** Morphisms *)

  Record m α β :=
    {
      fw : strat α -> strat β;
      bw : strat α -> costrat β -> costrat α;
      is_better : forall u y, α u (bw u y) -> β (fw u) y;
    }.

  Arguments fw {α β}.
  Arguments bw {α β}.

  (** Extensional equality *)

  Lemma mext {α β} (f g : m α β) :
    (forall u, fw f u = fw g u) ->
    (forall u y, bw f u y = bw g u y) ->
    f = g.
  Proof.
    destruct f as [f F ?], g as [g G ?]. cbn.
    intros Hfw Hbw.
    assert (g = f) by auto using functional_extensionality; subst.
    assert (G = F) by auto using functional_extensionality; subst.
    f_equal.
    apply functional_extensionality_dep; intro u.
    apply functional_extensionality_dep; intro y.
    apply functional_extensionality_dep; intro H.
    apply proof_irrelevance.
  Qed.


  (** ** Compositional structure *)

  Program Definition id α : m α α :=
    {|
      fw u := u;
      bw u x := x;
    |}.

  Program Definition compose {α β γ} (g : m β γ) (f : m α β) :=
    {|
      fw u := fw g (fw f u);
      bw u z := let v := fw f u in bw f u (bw g v z);
    |}.
  Next Obligation.
    auto using is_better.
  Qed.

  Lemma compose_id_l {α β} (f : m α β) :
    compose (id β) f = f.
  Proof.
    auto using mext.
  Qed.

  Lemma compose_id_r {α β} (f : m α β) :
    compose f (id α) = f.
  Proof.
    auto using mext.
  Qed.

  Lemma compose_assoc {α β γ δ} f g h :
    @compose α β δ (@compose β γ δ h g) f =
    @compose α γ δ h (@compose α β γ g f).
  Proof.
    auto using mext.
  Qed.


  (** ** Tensor product *)

  Definition one : t :=
    {|
      strat := unit;
      costrat := unit;
      winning _ _ := True;
    |}.

  Definition tens {I} (A : I -> t) : t :=
    {|
      strat := forall i, strat (A i);
      costrat := forall i, costrat (A i);
      winning u x := forall i, winning (A i) (u i) (x i);
    |}.

  Program Definition tens_m {I A B} (f : forall i:I, m (A i) (B i)) : m (tens A) (tens B) :=
    {|
      fw u := fun i => fw (f i) (u i);
      bw u x := fun i => bw (f i) (u i) (x i);
    |}.
  Next Obligation.
    auto using is_better.
  Qed.


  (** ** Internal hom *)

  Definition hom (A B : t) : t :=
    {|
      strat := strat A -> (strat B * (costrat B -> costrat A));
      costrat := strat A * costrat B;
      winning vx '(u, y) :=
        winning A u (snd (vx u) y) ->
        winning B (fst (vx u)) y;
    |}.

  (*
  Definition hom_m {A1 A2 B1 B2} (f : m A2 A1) (g : m B1 B2) : m (hom A1 B1) (hom A2 B2) :=
    {|
      fw uab1 ua2 :=
        let ua1 := fw f ua2 in
        let '(ub1, ka2) := uab1 (fw f ua2) in
*)        


  (** ** Cartesian product *)

  Definition top : t :=
    {|
      strat := unit;
      costrat := Empty_set;
      winning u x := match x with end;
    |}.

  Definition prod {I} (A : I -> t) :=
    {|
      strat := forall i, strat (A i);
      costrat := { i:I & costrat (A i) };
      winning u '(existT _ i x) := winning (A i) (u i) x;
    |}.

  Program Definition prod_m {I A B} (f : forall i:I, m (A i) (B i)) : m (prod A) (prod B) :=
    {|
      fw u := fun i => fw (f i) (u i);
      bw u '(existT _ i x) := existT _ i (bw (f i) (u i) x);
    |}.
  Next Obligation.
    auto using is_better.
  Qed.

End DSet.


(** * Sum-and-product completion of 2 (⊥ -> ⊤) *)

Module ΣΠ2.

  Record t :=
    {
      strat : Type;
      costrat : strat -> Type;
      winning :> forall σ : strat, costrat σ -> Prop;
    }.

  Record m α β :=
    {
      fw : strat α -> strat β;
      bw : forall σ : strat α, costrat β (fw σ) -> costrat α σ;
      is_better : forall u y, α u (bw u y) -> β (fw u) y;
    }.

  Arguments fw {α β}.
  Arguments bw {α β}.

  Lemma mext {α β} (f g : m α β) :
    (forall u, fw f u = fw g u) ->
    (forall u y H, bw f u y = bw g u (eq_rect _ _ y _ H)) ->
    f = g.
  Proof.
    destruct f as [f F ?], g as [g G ?]. cbn.
    intros Hfw Hbw.
    assert (g = f) by auto using functional_extensionality; subst.
    pose proof (fun u y => Hbw u y eq_refl) as Hbw_. cbn in *.
    assert (G = F) by auto using functional_extensionality_dep; subst.
    f_equal.
    apply functional_extensionality_dep; intro u.
    apply functional_extensionality_dep; intro y.
    apply functional_extensionality_dep; intro H.
    apply proof_irrelevance.
  Qed.

  Program Definition id α : m α α :=
    {|
      fw u := u;
      bw u x := x;
    |}.

  Program Definition compose {α β γ} (g : m β γ) (f : m α β) :=
    {|
      fw u := fw g (fw f u);
      bw u z := let v := fw f u in bw f u (bw g v z);
    |}.
  Next Obligation.
    auto using is_better.
  Qed.

  Lemma compose_id_l {α β} (f : m α β) :
    compose (id β) f = f.
  Proof.
    apply mext; cbn; auto. intros.
    replace H with (eq_refl (fw f u)) by apply proof_irrelevance; cbn.
    reflexivity.
  Qed.

  Lemma compose_id_r {α β} (f : m α β) :
    compose f (id α) = f.
  Proof.
    apply mext; cbn; auto. intros.
    replace H with (eq_refl (fw f u)) by apply proof_irrelevance; cbn.
    reflexivity.
  Qed.

  Lemma compose_assoc {α β γ δ} f g h :
    @compose α β δ (@compose β γ δ h g) f =
    @compose α γ δ h (@compose α β γ g f).
  Proof.
    apply mext; cbn; auto. intros.
    replace H with (eq_refl (fw h (fw g (fw f u)))) by apply proof_irrelevance; cbn.
    reflexivity.
  Qed.

  (** *** Tensor product *)

  Definition one : t :=
    {|
      strat := unit;
      costrat _ := unit;
      winning _ _ := True;
    |}.

  Definition tens {I} (A : I -> t) : t :=
    {|
      strat := forall i, strat (A i);
      costrat u := forall i, costrat (A i) (u i);
      winning u x := forall i, winning (A i) (u i) (x i);
    |}.

  Program Definition tens_m {I A B} (f : forall i:I, m (A i) (B i)) : m (tens A) (tens B) :=
    {|
      fw u := fun i => fw (f i) (u i);
      bw u x := fun i => bw (f i) (u i) (x i);
    |}.
  Next Obligation.
    auto using is_better.
  Qed.

  (** *** Internal hom *)

  Definition hom (A B : t) : t :=
    {|
      strat := forall u : strat A, { v : strat B & costrat B v -> costrat A u };
      costrat vx := { u : strat A & costrat B (projT1 (vx u)) };
      winning vx '(existT _ u y) :=
        winning A u (projT2 (vx u) y) ->
        winning B (projT1 (vx u)) y;
    |}.

  (*
  Definition hom_m {A1 A2 B1 B2} (f : m A2 A1) (g : m B1 B2) : m (hom A1 B1) (hom A2 B2) :=
    {|
      fw uab1 ua2 :=
        let ua1 := fw f ua2 in
        let '(ub1, ka2) := uab1 (fw f ua2) in
*)        

  (** *** Cartesian product *)

  Definition top : t :=
    {|
      strat := unit;
      costrat _ := Empty_set;
      winning u x := match x with end;
    |}.

  Definition prod {I} (A : I -> t) :=
    {|
      strat := forall i, strat (A i);
      costrat u := { i:I & costrat (A i) (u i) };
      winning u '(existT _ i x) := winning (A i) (u i) x;
    |}.

  Program Definition prod_m {I A B} (f : forall i:I, m (A i) (B i)) : m (prod A) (prod B) :=
    {|
      fw u := fun i => fw (f i) (u i);
      bw u '(existT _ i x) := existT _ i (bw (f i) (u i) x);
    |}.
  Next Obligation.
    auto using is_better.
  Qed.

End ΣΠ2.


(** * Jan's adaptation of Joyal's games *)

Module J.

  (** ** Games *)

  Inductive t :=
    | done (w : Prop)
    | branch {I} (ϵ : bool) (k : I -> t).

  (** Often, we will use the following notations to distinguish the
    two cases of the [branch] constructor. *)

  Notation sigma := (branch true).
  Notation pi := (branch false).

  (** Dialectica objects can be read as simple games involving
    a σ-move u ∈ U followed by a π-move x ∈ X. *)

  Definition of_dial (A : DSet.t) : t :=
    sigma (fun u =>
       pi (fun x =>
     done (DSet.winning A u x))).

  (** ** Strategies and costrategies *)

  Fixpoint strat (G : t) : Type :=
    match G with
      | done _ => unit
      | sigma k => {i & strat (k i)}
      | pi k => forall i, strat (k i)
    end.

  Fixpoint costrat (G : t) : Type :=
    match G with
      | done _ => unit
      | sigma k => forall i, costrat (k i)
      | pi k => {i & costrat (k i)}
    end.

  Fixpoint winning (G : t) : strat G -> costrat G -> Prop :=
    match G with
      | done w => fun _ _ => w
      | sigma k => fun '(existT _ i σ) π => winning (k i) σ (π i)
      | pi k => fun σ '(existT _ i π) => winning (k i) (σ i) π
    end.

  (** The set of strategies and costrategies together with the payoff
    function can be used to define a Dialectica object. *)

  Definition dial_of (G : t) : DSet.t :=
    {|
      DSet.strat := strat G;
      DSet.costrat := costrat G;
      DSet.winning := winning G;
    |}.

  (** We can also define winning strategies in the same way. *)

  Fixpoint wstrat (G : t) : Type :=
    match G with
      | done w => w
      | sigma k => {i & wstrat (k i)}
      | pi k => forall i, wstrat (k i)
    end.

  Fixpoint w_strat {G} : wstrat G -> strat G :=
    match G with
      | done w => fun _ => tt
      | sigma k => fun '(existT _ i u) => existT _ i (w_strat u)
      | pi k => fun u i => w_strat (u i)
    end.

  Coercion w_strat : wstrat >-> strat.

  Lemma wstrat_winning (G : t) (u : wstrat G) (x : costrat G) :
    winning G u x.
  Proof.
    induction G as [w | I [|] k]; auto.
    - destruct u as [i u]; cbn in *; auto.
    - destruct x as [i x]; cbn in *; auto.
  Qed.


  (** ** Tensor product *)

  (** The tensor product of games lets them be played side by side.
    The player σ takes priority and move when either game is of the
    form [Σi . Gi], but it must win both games to win overall.

    In this principle this can be defined in a straightforward way
    using a simple case analysis. Below I have elided the symmetric
    cases, and each line defines one layer of choice only, even when
    shown as ∑ + ∑.

        - ∑i·Gi ⊗ ∑j·Hj := ∑i·(Gi ⊗ ∑j·Hj) + ∑j·(∑i·Gi ⊗ Hj)
        - ∑i·Gi ⊗ ∏j·Hj := ∑i·(Gi ⊗ ∏j·Hj)
        - ∑i·Gi ⊗ win   := ∑i·(Gi ⊗ win)
        - ∑i·Gi ⊗ lose  := ∑i·(Gi ⊗ lose)
        - ∏i·Gi ⊗ ∏j·Hj := ∏i·(Gi ⊗ ∏j·Hj) × ∏j·(∏i·Gi ⊗ Hj)
        - ∏i·Gi ⊗ win   := ∏i·(Gi ⊗ win)
        - ∏i·Gi ⊗ lose  := ∏i·(Gi ⊗ lose)
        -   win ⊗ win   := win
        -   win ⊗ lose  := lose
        -  lose ⊗ lose  := lose

    While straightforward in principle, it is somewhat tricky
    to define in a way which makes termination evident to Coq,
    because only one of the two games will have a move "peeled off"
    at any given step. To make this work we use a sort of continuation
    passing style where two fixpoints communicate with each other
    while peeling off exactly one move at a time.

    Unfortunately, under this approach, the symmetry of the underlying
    process is not reflected by the structure of the definition.
    In the definition of [G ⊗ H], we will use separate cases depending
    on the structure of [G]. *)

  (** *** Tensoring with base games *)

  (** If [G] is at its conclusion, we finish playing [H] largely as-is,
    but adjust its payoff based on the outcome of [G]. *)

  Fixpoint tens_finish (Gw : Prop) (H : t) : t :=
    match H with
      | done Hw => done (Gw /\ Hw)
      | branch ϵ Hk => branch ϵ (fun i => tens_finish Gw (Hk i))
    end.

  (** *** Tensoring with σ-games *)

  (** When [G] is of the form [∑i·Gi], we must "mix in" any σ-moves
    that are available in [H] as well. The following definition helps. *)

  Definition sigma2 {I J} (Gk : I -> t) (Hk : J -> t) :=
    sigma (sum_rect _ Gk Hk).

  (** If σ chooses a move in [H], we continue with the corresponding
    subgame. When σ chooses (or is forced) to play in G, we invoke the
    corresponding "Gi continuation" and pass the residual [H]. *)

  Fixpoint tens_sigma {I} (Gk : I -> t -> t) (H : t) : t :=
    match H with
      | sigma Hk => sigma2 (fun i => Gk i H) (fun j => tens_sigma Gk (Hk j))
      | _        => sigma  (fun i => Gk i H)
    end.

  (** *** Tensoring with π-games *)

  (** When [G] is of the form [∏i·Gi], we must first exhaust all
    possible σ-moves in [H]. Control transfers to π only once we
    encounter a π-move in [H] as well, at which point we must mix in
    the available π-moves from [G]. *)

  Definition pi2 {I J} (Gk : I -> t) (Hk : J -> t) :=
    pi (sum_rect _ Gk Hk).

  (** Once again, when π chooses to move in [G], we invoke the
    corresponding continuation and pass to it the residual [H]. *)

  Fixpoint tens_pi {I} (Gk : I -> t -> t) (H : t) : t :=
    match H with
      | sigma Hk => sigma (fun j => tens_pi Gk (Hk j))
      | pi Hk => pi2 (fun i => Gk i H) (fun j => tens_pi Gk (Hk j))
      | _ => pi (fun i => Gk i H)
    end.

  (** *** Putting everything together *)

  (** With this, we are ready to do the case analysis and recursion
    on the game [G]. Termination checking works because instead of
    [tens_sigma] and [tens_pi] invoking [tens] on the subgames of [G]
    directly, they do it through a continuation which is defined within
    the scope of [tens] itself. *)

  Fixpoint tens (G : t) (H : t) :=
    match G with
      | done Gw  => tens_finish Gw H
      | sigma Gk => tens_sigma (fun i H' => tens (Gk i) H') H
      | pi Gk    => tens_pi    (fun i H' => tens (Gk i) H') H
    end.


  (** ** Negation *)

  (** The complement of a game exchanges the roles of the two players. *)

  Fixpoint opp (G : t) : t :=
    match G with
      | done w => done (~ w)
      | branch ϵ k => branch (negb ϵ) (fun i => opp (k i))
    end.
  

  (** ** Internal hom *)

  (** As expected, we can now describe the game used to construct
    morphisms using a combination of tensors and negation. *)

  Definition hom (G H : t) : t :=
    opp (tens G (opp H)).

  (** A morphism from [G] to [H] is then a winning strategy for [G ⊸ H]. *)

  Definition m (G H : t) : Type :=
    wstrat (hom G H).


  (** ** The happens-before game *)

  (*
  Fixpoint bef (G H : t) : t :=
    match G with
      | done _ => H
      | branch ϵ Gk => branch ϵ (fun i => bef (Gk i) H)
    end.

  Inductive seq : Type :=
    seq_nil : seq
  | seq_cons (I : Type) : seq.

  Fixpoint seqg (v : seq) :=
    match v with
      | seq_nil => done True
      | seq_cons I v => sigma 
*)
  


  (** ** Composition *)

  (** The identity strategy acts as a copycat. Because of the way
    [hom A B] is constructed, the opponent always start. One
    difficulty is that because games are not necessarily alternating,
    the opponent might be able to play multiple moves in a row before
    we get a change to repeat them. As a result the games become
    desynchronize and we must use some kind of "buffer" to defined the
    strategy. *)

  Inductive id_buffer :=
    | ibn : id_buffer
    | ibc {I : Set} (i : I) 

  Fixpoint id_def {G} (

  Fixpoint id {G} : m G G.
  Proof.
    
    induction G as [W | I [|] G]; cbn in *.
    - abstract tauto.
    - intro i. (* played by opponent on the left *)
      specialize (X i).

cbn in *.
      
      match G with
      | done w => 

  (** Composition gets complicated as 
  Definition compose {E F G} (g : m F G) (f : m E F) : m E G.
  Proof.
    unfold m, hom in *.
    unfold wstrat in g, f.
    cbn in *.
    do 2 red in g, f.
    cbn in *.










(** * Intuitionistic games *)

Module IntGame.

  (** ** Game shapes *)

  Inductive t :=
    | nil
    | cons {I} (next : I -> t).

  Fixpoint strat (G : t) : Type :=
    match G with
      | nil => unit
      | cons next => {i & costrat (next i)}
    end
  with costrat (G : t) :=
    match G with
      | nil => unit
      | cons next => forall i, strat (next i)
    end.

  Fixpoint eval (G : t) : strat G -> costrat G -> Prop :=
    match G with
      | nil => fun _ _ => True
      | cons next => fun '(existT _ i u) x => coeval (next i) u (x i)
    end
  with coeval (G : t) : costrat G -> strat G -> Prop :=
    match G with
      | nil => fun _ _ => False
      | cons next => fun u '(existT _ i x) => eval (next i) (u i) x
    end.

  



  (** ** Games *)

  Inductive game :=
    | done (w : Prop)
    | round {I J} (cont : forall i:I, J i -> game).

  (** *** Mapping games to Dialectica *)

  (** We compute the sets of stratgies, costrategies, and an
    evaluation function which plays one against the other. *)

  Inductive branch {I J} (A : forall i, J i -> Type) : Type :=
    | br (i:I) : (forall j : J i, A i j) -> branch A.

  Fixpoint gstrat (G : game) : Type :=
    match G with
      | done _ => unit
      | round cont => branch (fun i j => gstrat (cont i j))
    end.

  Fixpoint gcostrat (G : game) : Type :=
    match G with
      | done _ => unit
      | round cont => forall i, {j & gcostrat (cont i j)}
    end.

  Fixpoint outcome (G : game) : gstrat G -> gcostrat G -> Prop :=
    match G with
      | done b => (fun 'tt 'tt => b)
      | round cont =>
        fun σ π =>
          let '(br _ i σk) := σ in
          let '(existT _ j πk) := π i in
          outcome (cont i j) (σk j) πk
    end.

  Definition dial_of (G : game) : t :=
    {|
      strat := gstrat G;
      costrat := gcostrat G;
      winning := outcome G;
    |}.

  (** *** Dialectica to games *)

  Definition game_of (A : t) :=
    @round (strat A) (fun _ => costrat A) (fun u x => done (winning A u x)).


  (** ** Homomorphism of games *)

  Fixpoint ghom (G H : game) :=
    
