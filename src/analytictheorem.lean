import contourintegral
import rectangle_and_cauchytheorem
noncomputable theory

/- Define paths -/
def C1 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):= rec_bottom (-δ) (-R) R
def C2 {R:ℝ}(Rp: R>0):= rec_right (-R) R R
def C3 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):= rec_top R R (-δ)
def C4 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):= rec_left R (-δ) (-R)

def C_path {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):= 
  rectangle (-R) R R (-δ)

/- Define regions -/
def right_half (ε:ℝ) : set ℂ := {z:ℂ | z.re > -ε}

/- Define functions and Integrals -/
def g (f: ℝ → ℝ)(z:ℂ): ℂ := 
  ∫ (t : ℝ) in set.Ioi 0, ((f t)* complex.exp(-t*z))

def gT (f: ℝ → ℝ){T:ℝ}(Tp: T > 0)(z:ℂ): ℂ := 
  ∫ (t : ℝ) in 0..T, ((f t)* complex.exp(-t*z))

variables {f: ℝ → ℝ}(bounded: ∃ M:ℝ, ∀ t:ℝ, t≥0 → |f(t)| <M)
(locally_integrable: ∀ A:ℝ, A>0 → interval_integrable f 
measure_theory.measure_space.volume 0 A)

lemma gT_well_defined {T:ℝ}(Tp: T > 0)(z:ℂ): interval_integrable 
((λt:ℝ,  ((f t) * complex.exp(-t*z)) ):ℝ → ℂ)
measure_theory.measure_space.volume 0 T :=
begin
  sorry,
end

lemma gT_differentiable {T:ℝ}(Tp: T > 0): differentiable ℂ (gT f Tp):=
begin
  sorry,
end

lemma gT_continuous{T:ℝ}(Tp: T > 0): continuous (gT f Tp) :=
  by {exact differentiable.continuous (gT_differentiable Tp),}

variables
(g_holo: differentiable_on ℂ (g f) (right_half 0))
(extend_holo: ∃ g_extend:ℂ → ℂ, ∃ U:set ℂ, 
  is_open U ∧ (right_half 0) ⊂ U ∧ 
  set.eq_on (g_extend) (g f) (right_half 0) ∧ 
  differentiable_on ℂ (g_extend) U)

theorem analytic_theorem : measure_theory.integrable_on 
f (set.Ioi 0) measure_theory.measure_space.volume ∧  
( ∀ g_extend:ℂ → ℂ, (∃ U:set ℂ, 
  is_open U ∧ (right_half 0) ⊂ U ∧ 
  set.eq_on (g_extend) (g f) (right_half 0) ∧ 
  differentiable_on ℂ (g_extend) U) → 
((∫ (t : ℝ) in set.Ioi 0, (f t)):ℂ) = (g_extend 0) ) :=
begin
  sorry,
end
