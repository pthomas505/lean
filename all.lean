import tactic


lemma not_not_1 {P : Prop} : ¬ ¬ P → P :=
assume a1 :  ¬ ¬ P,
by_contradiction (
  assume a2 : ¬ P,
  show false, from a1 a2
)

lemma not_not_2 {P : Prop} : P → ¬ ¬ P :=
assume a1 : P,
assume a2 : ¬ P,
show false, from a2 a1

lemma not_not' {P : Prop} : ¬ ¬ P ↔ P :=
iff.intro not_not_1 not_not_2

--------------------------------------------------------------------------------

lemma contrapose_1 {P Q : Prop} : (P → Q) → (¬ Q → ¬ P) :=
assume a1 : P → Q,
assume a2: ¬ Q,
by_contradiction (
  assume a3 : ¬ ¬ P,
  have s1 : P := not_not_1 a3,
  have s2 : Q := a1 s1,
  show false, from a2 s2
)

lemma contrapose_2 {P Q : Prop} : (P → ¬ Q) → (Q → ¬ P) :=
assume a1 : P → ¬ Q,
assume a2 : Q,
by_contradiction (
  assume a3 : ¬ ¬ P,
  have s1 : P := not_not_1 a3,
  have s2 : ¬ Q := a1 s1,
  show false, from s2 a2
)

lemma contrapose_3 {P Q : Prop} : (¬ P → Q) → (¬ Q → P) :=
assume a1 : ¬ P → Q,
assume a2 : ¬ Q,
by_contradiction (
  assume a3 : ¬ P,
  have s1 : Q := a1 a3,
  show false, from a2 s1
)

lemma contrapose_4 {P Q : Prop} : (¬ P → ¬ Q) → (Q → P) :=
assume a1 : ¬ P → ¬ Q,
assume a2 : Q,
by_contradiction (
  assume a3 : ¬ P,
  have s1 : ¬ Q := a1 a3,
  show false, from s1 a2
)

--------------------------------------------------------------------------------

lemma dm_1_a {P Q : Prop} : ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) :=
assume a1 : ¬ (P ∧ Q),
by_contradiction (
  assume a2 : ¬ (¬ P ∨ ¬ Q),
  have s1 : P := (
    by_contradiction (
      assume a3 : ¬ P,
      have s2 : ¬ P ∨ ¬ Q := or.intro_left (¬ Q) a3,
      show false, from a2 s2
    )
  ),
  have s3 : Q := (
    by_contradiction (
      assume a4 : ¬ Q,
      have s4 : ¬ P ∨ ¬ Q := or.intro_right (¬ P) a4,
      show false, from a2 s4
    )
  ),
  have s5 : P ∧ Q := and.intro s1 s3,
  show false, from a1 s5
)

lemma dm_1_b {P Q : Prop} : ¬ (P ∧ ¬ Q) → (¬ P ∨ Q) :=
assume a1 : ¬ (P ∧ ¬ Q),
by_contradiction (
  assume a2 : ¬ (¬ P ∨ Q),
  have s1 : P := (
    by_contradiction (
      assume a3 : ¬ P,
      have s2 : ¬ P ∨ Q := or.intro_left Q a3,
      show false, from a2 s2
    )
  ),
  have s3 : ¬ Q := (
    by_contradiction (
      assume a4 : ¬ ¬ Q,
      have s4 : Q := not_not_1 a4,
      have s5 : ¬ P ∨ Q := or.intro_right (¬ P) s4,
      show false, from a2 s5
    )
  ),
  have s6 : P ∧ ¬ Q := and.intro s1 s3,
  show false, from a1 s6
)

lemma dm_1_c {P Q : Prop} : ¬ (¬ P ∧ Q) → (P ∨ ¬ Q) :=
assume a1 : ¬ (¬ P ∧ Q),
by_contradiction (
  assume a2 : ¬ (P ∨ ¬ Q),
  have s1 : ¬ P := (
    by_contradiction (
      assume a3 : ¬ ¬ P,
      have s2 : P := not_not_1 a3,
      have s3 : P ∨ ¬ Q := or.intro_left (¬ Q) s2,
      show false, from a2 s3
    )
  ),
  have s4 : Q := (
    by_contradiction (
      assume a4 : ¬ Q,
      have s5 : P ∨ ¬ Q := or.intro_right P a4,
      show false, from a2 s5
    )
  ),
  have s6 : ¬ P ∧ Q := and.intro s1 s4,
  show false, from a1 s6
)

lemma dm_1_d {P Q : Prop} : ¬ (¬ P ∧ ¬ Q) → (P ∨ Q) :=
assume a1 : ¬ (¬ P ∧ ¬ Q),
by_contradiction (
  assume a2 : ¬ (P ∨ Q),
  have s1 : ¬ P := (
    by_contradiction (
      assume a3 : ¬ ¬ P,
      have s2 : P := not_not_1 a3,
      have s3 : P ∨ Q := or.intro_left Q s2,
      show false, from a2 s3
    )
  ),
  have s4 : ¬ Q := (
    by_contradiction (
      assume a4 : ¬ ¬ Q,
      have s5 : Q := not_not_1 a4,
      have s6 : P ∨ Q := or.intro_right P s5,
      show false, from a2 s6
    )
  ),
  have s7 : ¬ P ∧ ¬ Q := and.intro s1 s4,
  show false, from a1 s7
)


lemma dm_2_a {P Q : Prop} : (¬ P ∨ ¬ Q) → ¬ (P ∧ Q) :=
assume a1 : ¬ P ∨ ¬ Q,
assume a2 : P ∧ Q,
or.elim a1
(
  assume a3 : ¬ P,
  have s1 : P := and.left a2,
  show false, from a3 s1
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a2,
  show false, from a4 s2
)

lemma dm_2_b {P Q : Prop} : (¬ P ∨ Q) → ¬ (P ∧ ¬ Q) :=
assume a1 : ¬ P ∨ Q,
assume a2 : P ∧ ¬ Q,
or.elim a1
(
  assume a3 : ¬ P,
  have s1 : P := and.left a2,
  show false, from a3 s1
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a2,
  show false, from s2 a4
)

lemma dm_2_c {P Q : Prop} : (P ∨ ¬ Q) → ¬ (¬ P ∧ Q) :=
assume a1 : P ∨ ¬ Q,
assume a2 : ¬ P ∧ Q,
or.elim a1
(
  assume a3 : P,
  have s1 : ¬ P := and.left a2,
  show false, from s1 a3
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a2,
  show false, from a4 s2
)

lemma dm_2_d {P Q : Prop} : (P ∨ Q) → ¬ (¬ P ∧ ¬ Q) :=
assume a1 : P ∨ Q,
assume a2 : ¬ P ∧ ¬ Q,
or.elim a1
(
  assume a3 : P,
  have s1 : ¬ P := and.left a2,
  show false, from s1 a3
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a2,
  show false, from s2 a4
)

lemma dm_a {P Q : Prop} : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) :=
iff.intro dm_1_a dm_2_a


lemma dm_3_a {P Q : Prop} : ¬ (P ∨ Q) → (¬ P ∧ ¬ Q) :=
assume a1 : ¬ (P ∨ Q),
have s1 : ¬ P := (
  by_contradiction (
    assume a2 : ¬ ¬ P,
    have s2 : P := not_not_1 a2,
    have s3 : P ∨ Q := or.intro_left Q s2,
    show false, from a1 s3
  )
),
have s4 : ¬ Q := (
  by_contradiction (
    assume a3 : ¬ ¬ Q,
    have s5 : Q := not_not_1 a3,
    have s6 : P ∨ Q := or.intro_right P s5,
    show false, from a1 s6
  )
),
and.intro s1 s4

lemma dm_3_b {P Q : Prop} : ¬ (P ∨ ¬ Q) → (¬ P ∧ Q) :=
assume a1 : ¬ (P ∨ ¬ Q),
have s1 : ¬ P := (
  by_contradiction (
    assume a2 : ¬ ¬ P,
    have s2 : P := not_not_1 a2,
    have s3 : P ∨ ¬ Q := or.intro_left (¬ Q) s2,
    show false, from a1 s3
  )
),
have s4 : Q := (
  by_contradiction (
    assume a3 : ¬ Q,
    have s5 : P ∨ ¬ Q := or.intro_right P a3,
    show false, from a1 s5
  )
),
and.intro s1 s4

lemma dm_3_c {P Q : Prop} : ¬ (¬ P ∨ Q) → (P ∧ ¬ Q) :=
assume a1 : ¬ (¬ P ∨ Q),
have s1 : P := (
  by_contradiction (
    assume a2 : ¬ P,
    have s2 : ¬ P ∨ Q := or.intro_left Q a2,
    show false, from a1 s2
  )
),
have s3 : ¬ Q := (
  by_contradiction (
    assume a3 : ¬ ¬ Q,
    have s4 : Q := not_not_1 a3,
    have s5 : ¬ P ∨ Q := or.intro_right (¬ P) s4,
    show false, from a1 s5
  )
),
and.intro s1 s3

lemma dm_3_d {P Q : Prop} : ¬ (¬ P ∨ ¬ Q) → (P ∧ Q) :=
assume a1 : ¬ (¬ P ∨ ¬ Q),
have s1 : P := (
  by_contradiction (
    assume a2 : ¬ P,
    have s2 : ¬ P ∨ ¬ Q := or.intro_left (¬ Q) a2,
    show false, from a1 s2
  )
),
have s3 : Q := (
  by_contradiction (
    assume a3 : ¬ Q,
    have s4 : ¬ P ∨ ¬ Q := or.intro_right (¬ P) a3,
    show false, from a1 s4
  )
),
and.intro s1 s3


lemma dm_4_a {P Q : Prop} : (¬ P ∧ ¬ Q) → ¬ (P ∨ Q) :=
assume a1 : ¬ P ∧ ¬ Q,
assume a2 : P ∨ Q,
or.elim a2
(
  assume a3 : P,
  have s1 : ¬ P := and.left a1,
  show false, from s1 a3
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a1,
  show false, from s2 a4
)

lemma dm_4_b {P Q : Prop} : (¬ P ∧ Q) → ¬ (P ∨ ¬ Q) :=
assume a1 : ¬ P ∧ Q,
assume a2 : P ∨ ¬ Q,
or.elim a2
(
  assume a3 : P,
  have s1 : ¬ P := and.left a1,
  show false, from s1 a3
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a1,
  show false, from a4 s2
)

lemma dm_4_c {P Q : Prop} : (P ∧ ¬ Q) → ¬ (¬ P ∨ Q) :=
assume a1 : P ∧ ¬ Q,
assume a2 : ¬ P ∨ Q,
or.elim a2
(
  assume a3 : ¬ P,
  have s1 : P := and.left a1,
  show false, from a3 s1
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a1,
  show false, from s2 a4
)

lemma dm_4_d {P Q : Prop} : (P ∧ Q) → ¬ (¬ P ∨ ¬ Q) :=
assume a1 : P ∧ Q,
assume a2 : ¬ P ∨ ¬ Q,
or.elim a2
(
  assume a3 : ¬ P,
  have s1 : P := and.left a1,
  show false, from a3 s1
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a1,
  show false, from a4 s2
)

lemma dm_b {P Q : Prop} : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) :=
iff.intro dm_3_a dm_4_a

--------------------------------------------------------------------------------

lemma dm_quant_cp_1 {α : Type} {P : α → Prop} : ¬ (∃ x : α, ¬ P x) → (∀ x : α, P x) :=
assume a1 : ¬ (∃ x : α, ¬ P x),
assume x' : α,
by_contradiction (
  assume a2 : ¬ P x',
  have s1 : ∃ x : α, ¬ P x := exists.intro x' a2,
  show false, from a1 s1
)

lemma dm_quant_1 {α : Type} {P : α → Prop} : ¬ (∀ x : α, P x) → (∃ x : α, ¬ P x) :=
contrapose_3 dm_quant_cp_1

lemma dm_quant_2 {α : Type} {P : α → Prop} : (∃ x : α, ¬ P x) → ¬ (∀ x : α, P x) :=
assume a1 : ∃ x : α, ¬ P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : ¬ P x',
  assume a3 : ∀ x : α, P x,
  have s1 : P x' := a3 x',
  show false, from a2 s1
)

lemma dm_quant_a {α : Type} {P : α → Prop} : ¬ (∀ x : α, P x) ↔ (∃ x : α, ¬ P x) :=
iff.intro dm_quant_1 dm_quant_2


lemma dm_quant_3 {α : Type} {P : α → Prop} : ¬ (∃ x : α, P x) → (∀ x : α, ¬ P x) :=
assume a1 : ¬ (∃ x : α, P x),
assume x' : α,
by_contradiction (
  assume a2 : ¬ ¬ P x',
  have s1 : P x' := not_not_1 a2,
  have s2 : ∃ x : α, P x := exists.intro x' s1,
  show false, from a1 s2
)

lemma dm_quant_4 {α : Type} {P : α → Prop} : (∀ x : α, ¬ P x) → ¬ (∃ x : α, P x) :=
assume a1 : ∀ x : α, ¬ P x,
assume a2 : ∃ x : α, P x,
exists.elim a2 (
  assume x' : α,
  assume a3 : P x',
  have s1 : ¬ P x' := a1 x',
  show false, from s1 a3
)

lemma dm_quant_b {α : Type} {P : α → Prop} : ¬ (∃ x : α, P x) ↔ (∀ x : α, ¬ P x) :=
iff.intro dm_quant_3 dm_quant_4

--------------------------------------------------------------------------------

lemma dm_quant_set_cp_1 {α : Type} {S : set α} {P : α → Prop} : ¬ (∃ x ∈ S, ¬ P x) → (∀ x ∈ S, P x) :=
assume a1 : ¬ (∃ x ∈ S, ¬ P x),
assume x' : α,
assume a2 : x' ∈ S,
by_contradiction (
  assume a3 : ¬ P x',
  have s1 : ∃ x ∈ S, ¬ P x := exists.intro x' (exists.intro a2 a3),
  show false, from a1 s1
)

lemma dm_quant_set_1 {α : Type} {S : set α} {P : α → Prop} : ¬ (∀ x ∈ S, P x) → (∃ x ∈ S, ¬ P x) :=
contrapose_3 dm_quant_set_cp_1

lemma dm_quant_set_2 {α : Type} {S : set α} {P : α → Prop} : (∃ x ∈ S, ¬ P x) → ¬ (∀ x ∈ S, P x) :=
assume a1 : ∃ x ∈ S, ¬ P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : ∃ (H : x' ∈ S), ¬ P x',
  exists.elim a2 (
    assume H0 : x' ∈ S,
    assume a3 : ¬ P x',
    assume a4 : ∀ x ∈ S, P x,
    have s1 : P x' := a4 x' H0,
    show false, from a3 s1
  )
)

lemma dm_quant_set_a {α : Type} {S : set α} {P : α → Prop} : ¬ (∀ x ∈ S, P x) ↔ (∃ x ∈ S, ¬ P x) :=
iff.intro dm_quant_set_1 dm_quant_set_2


lemma dm_quant_set_3 {α : Type} {S : set α} {P : α → Prop} : ¬ (∃ x ∈ S, P x) → (∀ x ∈ S, ¬ P x) :=
assume a1 : ¬ (∃ x ∈ S, P x),
assume x' : α,
assume a2 : x' ∈ S,
by_contradiction (
  assume a3 : ¬ ¬ P x',
  have s1 : P x' := not_not_1 a3,
  have s2 : ∃ x ∈ S, P x := exists.intro x' (exists.intro a2 s1),
  show false, from a1 s2
)

lemma dm_quant_set_4 {α : Type} {S : set α} {P : α → Prop} : (∀ x ∈ S, ¬ P x) → ¬ (∃ x ∈ S, P x) :=
assume a1 : ∀ x ∈ S, ¬ P x,
assume a2 : ∃ x ∈ S, P x,
exists.elim a2 (
  assume x' : α,
  assume a3 : ∃ (H : x' ∈ S), P x',
  exists.elim a3 (
    assume H0 : x' ∈ S,
    assume a4 : P x',
    have s1 : ¬ P x' := a1 x' H0,
    show false, from s1 a4
  )
)

lemma dm_quant_set_b {α : Type} {S : set α} {P : α → Prop} : ¬ (∃ x ∈ S, P x) ↔ (∀ x ∈ S, ¬ P x) :=
iff.intro dm_quant_set_3 dm_quant_set_4

--------------------------------------------------------------------------------

example {α : Type} {P Q : α → Prop} (h : ∀ x : α, P x → Q x) : (∀ x : α, P x) → (∀ x : α, Q x) :=
assume a1 : ∀ x : α, P x,
assume x' : α,
have s1 : P x' := a1 x',
have s2 : P x' → Q x' := h x',
s2 s1

example {α : Type} {S : set α} {P Q : α → Prop} (h : ∀ x ∈ S, P x → Q x) : (∀ x ∈ S, P x) → (∀ x ∈ S, Q x) :=
assume a1 : ∀ x ∈ S, P x,
assume x' : α,
assume a2 : x' ∈ S,
have s1 : P x' := a1 x' a2,
have s2 : P x' → Q x' := h x' a2,
s2 s1


example {α : Type} {P Q : α → Prop} (h : ∀ x : α, P x → Q x) : (∃ x : α, P x) → (∃ x : α, Q x) :=
assume a1 : ∃ x : α, P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : P x',
  have s1 : P x' → Q x' := h x',
  have s2 : Q x' := s1 a2,
  exists.intro x' s2
)

example {α : Type} {S : set α} {P Q : α → Prop} (h : ∀ x ∈ S, P x → Q x) : (∃ x ∈ S, P x) → (∃ x ∈ S, Q x) :=
assume a1 : ∃ x ∈ S, P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : ∃ (H : x' ∈ S), P x',
  exists.elim a2 (
    assume H0 : x' ∈ S,
    assume a3 : P x',
    have s1 : P x' → Q x' := h x' H0,
    have s2 : Q x' := s1 a3,
    exists.intro x' (exists.intro H0 s2)
  )
)

--------------------------------------------------------------------------------

lemma or_comm' {P Q : Prop} : (P ∨ Q) → (Q ∨ P) :=
assume a1 : P ∨ Q,
or.elim a1
(
  assume a2 : P,
  or.intro_right Q a2
)
(
  assume a3 : Q,
  or.intro_left P a3
)


lemma or_implies_1 {P Q : Prop} : (P ∨ Q) → ¬ P → Q :=
assume a1 : P ∨ Q,
assume a2 : ¬ P,
or.elim a1
(
  assume a3 : P,
  false.elim (a2 a3)
)
(
  assume a4 : Q,
  a4
)

lemma or_implies_2 {P Q : Prop} : (P ∨ ¬ Q) → ¬ P → ¬ Q :=
assume a1 : P ∨ ¬ Q,
assume a2 : ¬ P,
or.elim a1
(
  assume a3 : P,
  false.elim (a2 a3)
)
(
  assume a4 : ¬ Q,
  a4
)

lemma or_implies_3 {P Q : Prop} : (¬ P ∨ Q) → P → Q :=
assume a1 : ¬ P ∨ Q,
assume a2 : P,
or.elim a1
(
  assume a3 : ¬ P,
  false.elim (a3 a2)
)
(
  assume a4 : Q,
  a4
)

lemma or_implies_4 {P Q : Prop} : (¬ P ∨ ¬ Q) → P → ¬ Q :=
assume a1 : ¬ P ∨ ¬ Q,
assume a2 : P,
or.elim a1
(
  assume a3 : ¬ P,
  false.elim (a3 a2)
)
(
  assume a4 : ¬ Q,
  a4
)

--------------------------------------------------------------------------------

lemma not_and_implies_1 {P Q : Prop} : ¬ (P ∧ Q) → P → ¬ Q :=
assume a1 : ¬ (P ∧ Q),
or_implies_4 (dm_1_a a1)

lemma not_and_implies_2 {P Q : Prop} : ¬ (P ∧ Q) → Q → ¬ P :=
assume a1 : ¬ (P ∧ Q),
or_implies_4 (or_comm' (dm_1_a a1))


lemma not_and_implies_3 {P Q : Prop} : ¬ (P ∧ ¬ Q) → P → Q :=
assume a1 : ¬ (P ∧ ¬ Q),
or_implies_3 (dm_1_b a1)

lemma not_and_implies_4 {P Q : Prop} : ¬ (P ∧ ¬ Q) → ¬ Q → ¬ P :=
assume a1 : ¬ (P ∧ ¬ Q),
or_implies_2 (or_comm' (dm_1_b a1))


lemma not_and_implies_5 {P Q : Prop} : ¬ (¬ P ∧ Q) → ¬ P → ¬ Q :=
assume a1 : ¬ (¬ P ∧ Q),
or_implies_2 (dm_1_c a1)

lemma not_and_implies_6 {P Q : Prop} : ¬ (¬ P ∧ Q) → Q → P :=
assume a1 : ¬ (¬ P ∧ Q),
or_implies_3 (or_comm' (dm_1_c a1))


lemma not_and_implies_7 {P Q : Prop} : ¬ (¬ P ∧ ¬ Q) → ¬ P → Q :=
assume a1 : ¬ (¬ P ∧ ¬ Q),
or_implies_1 (dm_1_d a1)

lemma not_and_implies_8 {P Q : Prop} : ¬ (¬ P ∧ ¬ Q) → ¬ Q → P :=
assume a1 : ¬ (¬ P ∧ ¬ Q),
or_implies_1 (or_comm' (dm_1_d a1))

--------------------------------------------------------------------------------

def set' (α : Type) := α → Prop

-- a is an element of the set s.
def mem' {α : Type} (a : α) (s : set α) : Prop := s a

-- The set containing only a.
def singleton' {α : Type} (a : α) : set' α := fun x, x = a

example {α : Type} {a b : α} : mem' a (singleton' b) = (a = b) := by refl


-- The union of the sets s and t.
def union' {α : Type} (s t : set' α) : set' α :=
fun x, (mem' x s) ∨ (mem' x t)

example {α : Type} {s t : set α} {x : α} : mem' x (union' s t) = ((mem' x s) ∨ (mem' x t)) := by refl


-- The intersection of the sets s and t.
def inter' {α : Type} (s t : set α) : set α :=
fun x, (mem' x s) ∧ (mem' x t)

example {α : Type} {s t : set α} {x : α} : mem' x (inter' s t) = ((mem' x s) ∧ (mem' x t)) := by refl


-- The difference of the sets s and t.
def diff' {α : Type} (s t : set α) : set α :=
fun x, (mem' x s) ∧ ¬ (mem' x t)

example {α : Type} {s t : set α} {x : α} : mem' x (diff' s t) = ((mem' x s) ∧ ¬ (mem' x t)) := by refl


-- The complement of the set s.
def compl' {α : Type} (s : set α) : set α :=
fun x, ¬ mem' x s

example {α : Type} {s t : set α} {x : α} : mem' x (compl' s) = ¬ mem' x s := by refl

--------------------------------------------------------------------------------

class left_group (G : Type*) :=
(op : G → G → G)
(e : G)
(assoc : ∀ a b c : G, op a (op b c) = op (op a b) c)
(op_unit : ∀ a : G, op e a = a)
(op_inv : ∀ a : G, ∃ a' : G, op a' a = e)

open left_group

example {G : Type*} [left_group G] : ∀ a : G, ∃ a' : G, op a a' = e :=
have s1 : ∀ a : G, ∃ a' : G, op a' a = e := op_inv,
assume a : G,
have s2 : ∃ a' : G, op a' a = e := s1 a,
exists.elim s2 (
  assume a' : G,
  assume a1 : op a' a = e,
  let y := op a a' in
  have s3 : op y y = y := (
    calc
    op y y = op (op a a') (op a a') : by refl
    ... = op a (op a' (op a a')) : by exact eq.symm (assoc a a' (op a a'))
    ... = op a (op (op a' a) a') : by rewrite (assoc a' a a')
    ... = op a (op e a') : by rewrite a1
    ... = op a a' : by rewrite (op_unit a')
    ... = y : by refl
  ),
  have s4 : ∃ y' : G, op y' y = e := op_inv y,
  exists.elim s4 (
    assume y' : G,
    assume a2 : op y' y = e,
    have s5 : op a a' = e := (
    calc
    op a a' = y : by refl
    ... = op e y : by exact eq.symm (op_unit y)
    ... = op (op y' y) y : by rewrite a2
    ... = op y' (op y y) : by exact eq.symm (assoc y' y y)
    ... = op y' y : by rewrite s3
    ... = e : by exact a2
    ),
    exists.intro a' s5
  )
)

--------------------------------------------------------------------------------

def var := ℕ

inductive pre_term : Type
| var : var → pre_term
| app : pre_term → pre_term → pre_term
| abs : var → pre_term → pre_term

notation `λ` y `.` P := pre_term.abs y P


def FV : pre_term → set var
| (pre_term.var x) := {x}
| (pre_term.app P Q) := (FV P) ∪ (FV Q)
| (pre_term.abs x P) := (FV P) \ {x}


-- sub_is_def M x N means M [ x := N ] is defined
inductive sub_is_def : pre_term → var → pre_term → Prop

-- y [ x := N ] is defined
| var (y : var) (x : var) (N : pre_term) :
  sub_is_def (pre_term.var y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app (P : pre_term) (Q : pre_term) (x : var) (N : pre_term) :
  sub_is_def P x N → sub_is_def Q x N → sub_is_def (pre_term.app P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_same (y : var) (P : pre_term) (x : var) (N : pre_term) :
  x = y → sub_is_def (pre_term.abs y P) x N

-- x ≠ y → x ∉ FV ( λ y . P ) → ( λ y . P ) [ x := N ] is defined
| abs_diff_nel (y : var) (P : pre_term) (x : var) (N : pre_term) :
  x ≠ y → x ∉ FV (pre_term.abs y P) → sub_is_def (pre_term.abs y P) x N

-- x ≠ y → y ∉ FV ( N ) → P [ x := N ] is defined → ( λ y . P ) [ x := N ] is defined
| abs_diff (y : var) (P : pre_term) (x : var) (N : pre_term) :
  x ≠ y → y ∉ FV N → sub_is_def P x N → sub_is_def (pre_term.abs y P) x N

notation M `[` x `:=` N `]` `is_def` := sub_is_def M x N


-- M [ x := N ]
def sub : pre_term → var → pre_term → pre_term
-- if x = y then y [ x := N ] = N else y [ x := N ] = y
| (pre_term.var y) x N := if (x = y) then N else (pre_term.var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| (pre_term.app P Q) x N := pre_term.app (sub P x N) (sub Q x N)

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P ) else ( λ y . P ) [ x := N ] = ( λ y . P [ x := N ] )
| (pre_term.abs y P) x N := if x = y then (pre_term.abs y P) else (pre_term.abs y (sub P x N))

notation M `[` x `:=` N `]` := sub M x N

