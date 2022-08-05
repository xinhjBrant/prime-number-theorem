import contourintegral
noncomputable theory

/- Define paths -/
def C1 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):=
  line_segment (-δ-R*complex.I) (R-R*complex.I)
def C2 {R:ℝ}(Rp: R>0):=
  line_segment (R-R*complex.I) (R+R*complex.I)
def C3 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):=
  line_segment (R+R*complex.I) (-δ+R*complex.I)
def C4 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):=
  line_segment (-δ+R*complex.I) (-δ-R*complex.I)

lemma join_to_C2 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0) : 
  (C1 Dp Rp) 1 = (C2 Rp) 0 :=
begin
  rw C1, rw C2, repeat {rw line_segment,}, simp, ring_nf,
end

def C1C2{δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0) :=
  path_concatenation (join_to_C2 Dp Rp) 

lemma join_to_C3 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0) : 
  (C1C2 Dp Rp) 1 = (C3 Dp Rp) 0 :=
begin
  rw C1C2, rw path_concatenation_endpoint _,
  rw C2, rw C3, repeat {rw line_segment,}, simp, ring_nf,
end

def C1C2C3{δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0) := 
  path_concatenation (join_to_C3 Dp Rp) 

lemma join_to_C4 {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0) : 
  (C1C2C3 Dp Rp) 1 = (C4 Dp Rp) 0 :=
begin
  rw C1C2C3, rw path_concatenation_endpoint _,
  rw C3, rw C4, repeat {rw line_segment,}, simp, ring_nf,
end

def C_path {δ:ℝ}(Dp: δ>0){R:ℝ}(Rp: R>0):= 
  path_concatenation (join_to_C4 Dp Rp) 

/- Define regions -/
def right_half (ε:ℝ) : set ℂ := {z:ℂ | z.re > -ε}

/- Define functions and Integrals -/
def g (f: ℝ → ℝ)(z:ℂ): ℂ := 
  ∫ (t : ℝ) in set.Ioi 0, ((f t)* complex.exp(-t*z))

def gT (f: ℝ → ℝ){T:ℝ}(Tp: T > 0)(z:ℂ): ℂ := 
  ∫ (t : ℝ) in 0..T, ((f t)* complex.exp(-t*z))

variables {f: ℝ → ℝ}(bounded: ∃ M:ℝ, ∀ t:ℝ, t≥0 → |f(t)| <M)
(locally_integrable: ∀ A:ℝ, A>0 → interval_integrable f measure_theory.measure_space.volume 0 A)

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
(extend_holo: ∃ g_extend:ℂ → ℂ, ∃ ε:ℝ, ε>0 ∧ 
  set.eq_on (g_extend) (g f) (right_half 0) ∧ 
  differentiable_on ℂ (g_extend) (right_half ε))

def g_extend:= extend_holo.some

theorem analytic_theorem :
measure_theory.integrable_on f (set.Ioi 0) measure_theory.measure_space.volume 
∧ (((∫ (t : ℝ) in set.Ioi 0, (f t)):ℂ) = (g_extend extend_holo 0))    :=
begin
  sorry,
end
