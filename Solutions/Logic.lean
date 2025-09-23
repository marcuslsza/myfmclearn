section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
    P → ¬ ¬ P  := by
  intro hp
  intro hNotP
  contradiction


theorem doubleneg_elim :
    ¬ ¬ P → P  := by
  intro hNotNotP
  by_cases hLem: P
  case pos =>
    assumption
  case neg =>
    have hBoom : False := hNotNotP hLem
    contradiction


theorem doubleneg_law :
    ¬ ¬ P ↔ P  := by
  constructor
  case mp =>
    intro hNotNotP
    by_cases hLem: P
    case pos =>
      assumption
    case neg =>
      have hBoom : False := hNotNotP hLem
      contradiction
  case mpr =>
    intro hp
    intro hnotP
    contradiction

------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
    (P ∨ Q) → (Q ∨ P)  := by
  intro hpvq
  rcases hpvq with (hp | hq)
  case inl =>
    right
    assumption
  case inr =>
    left
    assumption

theorem conj_comm :
    (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  rcases hpq with ⟨hp , hq⟩
  constructor
  case intro.left =>
    assumption
  case intro.right =>
    assumption


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
    (¬ P ∨ Q) → (P → Q)  := by
  intro h
  intro hp
  rcases h with (hNP | hQ)
  case inl =>
    have hboom : False := hNP hp
    contradiction
  case inr =>
    assumption




theorem disj_as_impl :
    (P ∨ Q) → (¬ P → Q)  := by
  intro hpvq
  intro hnp
  rcases hpvq with (hp | hq)
  case inl =>
    have hboom : False := hnp hp
    contradiction
  case inr =>
    assumption

------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
    (P → Q) → (¬ Q → ¬ P)  := by
  intro hpq
  intro hnq
  intro hp
  have hq : Q := hpq hp
  have hboom : False := hnq hq
  assumption



theorem impl_as_contrapositive_converse :
    (¬ Q → ¬ P) → (P → Q)  := by
  intro hnqnp
  intro hp
  by_cases hq : Q
  case pos =>
    assumption
  case neg =>
    have hnp : Not P := hnqnp hq
    contradiction



theorem contrapositive_law :
    (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor

  case mp =>
    intro hpq
    intro hnq
    intro hp
    have hq : Q := hpq hp
    have hboom : False := hnq hq
    assumption

  case mpr =>
    intro hnqnp
    intro hp
    by_cases hq : Q
    case pos =>
      assumption
    case neg =>
      have hnp : Not P := hnqnp hq
      contradiction


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
    ¬ ¬ (P ∨ ¬ P)  := by
  intro h
  apply h
  by_cases hLem: P
  case pos =>
    left
    assumption
  case neg =>
    right
    assumption
  --have hpnp : (P ∨ ¬P) := by

------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
    ((P → Q) → P) → ¬ ¬ P  := by
  intro h
  intro hnp
  apply hnp
  apply h
  intro hp
  contradiction

------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
    (P → Q) ∨ (Q → P)  := by
  by_cases hlem : Q
  case pos =>
    left
    intro hq
    assumption
  case neg =>
    right
    intro hq
    contradiction




------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
    P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro hpvq
  intro hnpnq
  rcases hnpnq with ⟨hnp,hnq⟩
  rcases hpvq with (hp | hq)
  case inl =>
    contradiction
  case inr =>
    contradiction


theorem conj_as_negdisj :
    P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro hpq
  intro hnpnq
  rcases hpq with ⟨hp,hq⟩
  rcases hnpnq with (hnp | hnq)
  case inl =>
    contradiction
  case inr =>
    contradiction



------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
    ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro hnpvq
  constructor
  case left =>
    intro hp
    apply hnpvq
    left
    assumption
  case right =>
    intro hq
    apply hnpvq
    right
    assumption


theorem demorgan_disj_converse :
    (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro hnpnq
  intro hpvq
  rcases hnpnq with ⟨hnp, hnq⟩
  rcases hpvq with (hp | hq)
  case intro.inl =>
    contradiction
  case intro.inr =>
    contradiction

theorem demorgan_conj :
    ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro hnpq
  by_cases hLemP : P
  case neg =>
    right
    assumption
  case pos =>
    by_cases hLemQ : Q
    case neg =>
      left
      assumption
    case pos =>
      have hpq : (P ∧ Q) := by
        constructor
        case left =>
          assumption
        case right =>
          assumption
      have hboom : False := hnpq hpq
      contradiction





theorem demorgan_conj_converse :
    (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro h
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  rcases h with (hnq | hnp)
  case intro.inl =>
    contradiction
  case intro.inr =>
    contradiction

theorem demorgan_conj_law :
    ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  case mpr =>
    intro h
    intro hpq
    rcases hpq with ⟨hp, hq⟩
    rcases h with (hnq | hnp)
    case intro.inl =>
      contradiction
    case intro.inr =>
      contradiction
  case mp =>
    intro hnpq
    by_cases hLemP : P
    case neg =>
      right
      assumption
    case pos =>
      by_cases hLemQ : Q
      case neg =>
        left
        assumption
      case pos =>
      have hpq : (P ∧ Q) := by
        constructor
        case left =>
          assumption
        case right =>
          assumption
      have hboom : False := hnpq hpq
      contradiction

theorem demorgan_disj_law :
    ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  case mp =>
    intro hnpvq
    constructor
    case left =>
      intro hp
      apply hnpvq
      left
      assumption
    case right =>
      intro hq
      apply hnpvq
      right
      assumption
  case mpr =>
  intro hnpnq
  intro hpvq
  rcases hnpnq with ⟨hnp, hnq⟩
  rcases hpvq with (hp | hq)
  case intro.inl =>
    contradiction
  case intro.inr =>
    contradiction

------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro h
  rcases h with ⟨hp, hqvr⟩
  rcases hqvr with (hq | hr)
  constructor
  case intro.inl.h =>
    constructor
    case left =>
      assumption
    case right =>
      assumption
  case intro.inr =>
    right
    constructor
    case h.left =>
      assumption
    case h.right =>
      assumption


theorem distr_conj_disj_converse :
    (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro h
  rcases h with (hl | hr)
  case inl =>
    rcases hl with ⟨hp, hq⟩
    constructor
    case intro.left =>
      assumption
    case intro.right =>
      left
      assumption
  case inr =>
    rcases hr with ⟨hp, hr⟩
    constructor
    case intro.left =>
      assumption
    case intro.right =>
      right
      assumption



theorem distr_disj_conj :
    P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro h
  rcases h with (hp | hqr)
  case inl =>
    constructor
    case left =>
      left
      assumption
    case right =>
      left
      assumption
  case inr =>
    rcases hqr with ⟨hq, hr⟩
    case intro =>
      constructor
      case left =>
        right
        assumption
      case right =>
        right
        assumption





theorem distr_disj_conj_converse :
    (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro h
  rcases h with ⟨hl, hr⟩
  rcases hl with (hp | hq)
  case intro.inl =>
    left
    assumption
  case intro.inr =>
    rcases hr with (hp | hr)
    case inl =>
      left
      assumption
    case inr =>
      right
      constructor
      case h.left =>
        assumption
      case h.right =>
        assumption

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
    ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro h
  intro hp
  intro hq
  have hpq : P ∧ Q := by
    constructor
    case left =>
      assumption
    case right =>
      assumption
  apply h
  assumption

theorem uncurry_prop :
    (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro h
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  case intro =>
  apply h
  case a =>
    assumption
  case a =>
    assumption



------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
    P → P  := by
  intro hp
  assumption


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
    P → (P ∨ Q)  := by
  intro hp
  left
  assumption

theorem weaken_disj_left :
    Q → (P ∨ Q)  := by
  intro hq
  right
  assumption

theorem weaken_conj_right :
    (P ∧ Q) → P  := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  case intro =>
    assumption

theorem weaken_conj_left :
    (P ∧ Q) → Q  := by
  intro hpq
  rcases hpq with ⟨hp,hq⟩
  case intro =>
    assumption


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
    (P ∨ P) ↔ P  := by
  constructor
  case mp =>
    intro hpvp
    rcases hpvp with (hp | hp)
    case inl =>
      assumption
    case inr =>
      assumption
  case mpr =>
    intro hp
    left
    assumption

theorem conj_idem :
    (P ∧ P) ↔ P := by
  constructor
  case mp =>
    intro hpp
    rcases hpp with ⟨hp1, hp2⟩
    case intro =>
      assumption
  case mpr =>
    intro hp
    constructor
    case left =>
      assumption
    case right =>
      assumption


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
    False → P := by
  intro hboom
  contradiction

theorem true_top :
    P → True  := by
  intro hp
  trivial

end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
    ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
    (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
    ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
    (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
    ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
    ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
    (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  intro h
  intro hnot
  obtain ⟨x, hpx⟩ := h
  have hnpx := hnot x
  contradiction

theorem forall_as_neg_exists :
    (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
    ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
    ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
    (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
    (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
    (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
    (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
    (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
    (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
    (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
    ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
    ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
    (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
    (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
