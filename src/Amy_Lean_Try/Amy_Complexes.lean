-- the result of trials by Ameena Hassan, 15th November 2018

import data.real.basic
-- not import data.complex.basic
import tactic.ring

structure complex : Type :=
(re : ℝ) (im : ℝ)
notation `∁` := complex

definition z : ∁ := ⟨5, 6⟩

definition z2: ∁ := {re := 5, im := 6}
--example : z = z2 := rfl

namespace complex

theorem ext (z w : ∁) : z.re = w.re ∧ z.im = w.im → z = w :=
begin
  cases z,
  cases w,
  intros,
  simp * at *,
end

instance : has_coe ℝ ∁ := ⟨λ x, {re := x, im := 0}⟩  

definition I : ∁ := ⟨0, 1⟩ 

definition add : ∁ → ∁ → ∁ := 
λ z w, ⟨z.re + w.re, z.im + w.im⟩ 

instance : has_add ∁ := ⟨complex.add⟩ 

@[simp] theorem add_re (z w : ∁) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : ∁) : (z + w).im = z.im + w.im := rfl 


theorem add_comm : ∀ z w : ∁, z + w = w + z :=
begin
  intros,
  apply ext,
  split,
  all_goals {simp},
end

theorem add_assoc : ∀ a b c : ∁, a + (b + c) = (a + b) + c :=
begin 
  intros,
  apply ext,
  split,
  all_goals {simp},
end

definition neg : ∁ → ∁ :=
λ z, ⟨-z.re, -z.im⟩ 

instance : has_neg ∁ := ⟨complex.neg⟩ 

@[simp] theorem neg_re (z : ∁) : (-z).re = -z.re := rfl 
@[simp] theorem neg_im (z : ∁) : (-z).im = -z.im := rfl 

definition mul : ∁ → ∁ → ∁ :=
λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ 

instance : has_mul ∁ := ⟨complex.mul⟩ 

@[simp] lemma mul_re (z w : ∁) : (z * w).re = (z.re * w.re - z.im * w.im) := rfl
@[simp] lemma mul_im (z w : ∁) : (z * w).im = (z.re * w.im + z.im * w.re) := rfl

theorem mul_assoc : ∀ a b c : ∁, a * (b * c) = (a * b) * c :=
begin 
  intros,
  apply ext,
  split, 
  all_goals {simp},
  all_goals {ring},
end

meta def CORIP : tactic unit := do
`[intros],
`[apply ext],
`[split],
`[all_goals {simp}],
`[all_goals {ring}]

theorem mul_assoc' (a b c : ∁) : a * (b * c) = (a * b) * c := by CORIP
theorem left_distrib (a b c : ∁) : a * (b + c) = a * b + a * c := by CORIP

@[simp] definition one : ∁ := ⟨1, 0⟩
@[simp] definition zero : ∁ := ⟨0, 0⟩  

theorem one_mul (a : ∁) : complex.one * a = a := by CORIP
theorem zero_mul (a : ∁) : complex.zero * a = zero := by CORIP

-- instance : comm_ring ∁ :=
-- by refine { mul := (*),
--   add := (+),
--   .. -- finilaize this part of mult one and mult zero
-- } 





end complex

-- theorem mul_assoc' (a b c : ∁) : a * (b*c) = (a*b)*c := by CORIP
-- theorem left_distrib (a b c : ∁) : a *(b+c) = a*b + a*c := by CORIP

-- @[simp] definition one : ∁ := (1, 0)
-- @[simp] definition zero : ∁ := (0, 0)

-- theorem one_mul (a : ∁) : complex.one * a = a := by CORIP
-- theorem zero_mul (a: ∁) : complex.zero * a = 0 := by CORIP

-- instance : comm_ring ∁ := 
-- by refine { mul := (*),
--   add := (+),
--   ..

-- }; {by CORIP}


















