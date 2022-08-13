import contourintegral
noncomputable theory

variables {E : Type} 
[normed_add_comm_group E] [normed_space ℂ E] [complete_space E] 

/-- Part I. Define line segments -/
def line_segment (a:ℂ) (b:ℂ) : ℝ → ℂ :=
  λ (θ : ℝ) , (b-a) * θ + a

/-- The derivative of the inclusion ℝ → ℂ is 1. --/
lemma coe_has_deriv (x:ℝ ):
has_deriv_at (λ (t : ℝ), (t : ℂ)) 1 x :=
begin
  rw has_deriv_at,
  rw has_deriv_at_filter_iff_is_o,
  simp,
end

lemma deriv_of_coe: deriv (λ (x : ℝ), (x : ℂ)) = 1 :=
begin
  exact deriv_eq coe_has_deriv,
end

/-- The line sgement and circle are both continuously differentiable. --/
lemma deriv_of_line (a:ℂ)(b:ℂ): 
  deriv (line_segment a b)  = constant_path (b-a):=
begin
  unfold line_segment constant_path,
  ext1,
  simp,
  rw deriv_of_coe,
  simp,
end

lemma deriv_of_line' (a:ℂ)(b:ℂ)(x : ℝ): 
  has_deriv_at (line_segment a b) (constant_path (b-a) x) x:=
begin
  unfold line_segment,
  have h0 : b - a = (b - a) + 0 := by simp,
  rw h0,
  apply has_deriv_at.add,
  have h2 : b - a = (1 : ℂ) • (b - a : ℂ) := by simp,
  rw h2,
  have h1 : (λ (x : ℝ), ((1 : ℂ) • (b - a) + 0) * ↑x) = (λ (x : ℂ), (b - a + 0) * x) ∘ (λ (x : ℝ), (x : ℂ)) := by simp,
  rw h1,
  apply has_deriv_at.scomp,
  {
    rw has_deriv_at,
    rw has_deriv_at_filter_iff_is_o,
    simp,
    have mid: (λ (x' : ℂ), (b - a) * x' - 
      (b - a) * ↑x - (x' - ↑x) * (b - a)) = 
      (λ(x:ℂ), (0:ℂ)) := by ring_nf,
    rw mid,
    rw asymptotics.is_o_const_left,
    left,
    exact rfl,
  },
  {
    simp,
    exact coe_has_deriv x,
  },
  {
    exact has_deriv_at_const x a,
  }
end

lemma line_is_differentiable (a:ℂ)(b:ℂ): 
  differentiable ℝ (line_segment a b):= 
begin
  unfold differentiable,
  intro x,
  apply has_deriv_at.differentiable_at (deriv_of_line' a b x),
end

lemma line_is_continuous (a:ℂ )(b:ℂ ):
  continuous (line_segment a b):=
  by {exact differentiable.continuous (line_is_differentiable a b),}

lemma line_is_in_C1 (a:ℂ )(b:ℂ):
  continuous (deriv (line_segment a b)):=
begin
  rw deriv_of_line a b,
  exact continuity_of_constant_path (b-a),
end

/-- Part II. Define rectangles -/
def rec_bottom (l:ℝ)(b:ℝ)(r:ℝ):=
  line_segment (l+b*complex.I) (r+b*complex.I)
def rec_right (b:ℝ)(r:ℝ)(t:ℝ):=
  line_segment (r+b*complex.I) (r+t*complex.I)
def rec_top (r:ℝ)(t:ℝ)(l:ℝ):=
  line_segment (r+t*complex.I) (l+t*complex.I)
def rec_left (t:ℝ)(l:ℝ)(b:ℝ):=
  line_segment (l+t*complex.I) (l+b*complex.I)

lemma bottom_join_right (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) : 
  rec_bottom l b r 1 = rec_right b r t 0:=
begin
  rw rec_bottom, rw rec_right, repeat {rw line_segment,}, 
  simp, ring_nf,
end 

def rec_bottomright (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) :=
  path_concatenation (bottom_join_right b r t l) 

lemma top_join_left (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) : 
  rec_top r t l 1 = rec_left t l b 0:=
begin
  rw rec_top, rw rec_left, repeat {rw line_segment,}, 
  simp, ring_nf,
end 

def rec_topleft (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) :=
  path_concatenation (top_join_left b r t l) 

lemma br_join_tl (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) :
  rec_bottomright b r t l 1 = rec_topleft b r t l 0 :=
begin
  rw [rec_bottomright, rec_topleft],
  rw path_concatenation_endpoint _,
  rw rec_right, rw path_concatenation, simp,
  rw rec_top, repeat {rw line_segment,}, simp, ring_nf,
end

def rectangle (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) := 
  path_concatenation (br_join_tl b r t l) 

/-- Part III. Define integrals along rectangles. -/
def complex_affine (α:ℂ)(c:ℂ):ℂ→ ℂ:=λz, α*z+c

lemma contour_integral_under_affine (f:ℂ → E)
(L:ℝ → ℂ)(α:ℂ)(c:ℂ):
  contour_integral f ((complex_affine α c)∘ L) = 
  α • contour_integral (f ∘ (complex_affine α c)) L :=
begin
  repeat {rw contour_integral},
  rw complex_affine,
  simp,
  rw smul_integral_convert,
  have l1: (λ t:ℝ, (α * deriv L t) • f (α * L t + c))
    = (λ t:ℝ, α •  deriv L t • f (α * L t + c)) :=
    by {ext1, rw smul_assoc_convert,},
  rw l1,
end

/- The contour integral along the sgements with both endpoints being real numbers is equal to the corresponding real integral. -/
lemma integral_along_reals (f:ℂ → E)(a:ℝ)(b:ℝ):
  contour_integral f (line_segment a b) = 
  ∫ (t: ℝ ) in a..b, f(t):=
begin
  unfold contour_integral,
  rw [deriv_of_line, constant_path, line_segment],
  simp,
  have h0 : ↑(b - a) = (b : ℂ) - (a : ℂ) := by simp,
  rw ←h0,
  cases decidable.em (b ≠ a) with heq hneq,
  {
    have h1 : (λ (x : ℝ), f (↑(b - a) * (x : ℂ) + (a : ℂ))) = (λ (x : ℝ), ((f ∘ λ (y : ℝ), (y : ℂ)) ((b - a) * x + a))) := by simp,
    have h2 : (λ (t : ℝ), f (t : ℂ)) = (λ (x : ℝ), ((f ∘ λ (y : ℝ), (y : ℂ)) x)) := by simp,
    rw [h1, h2],
    let g := (f ∘ λ (y : ℝ), (y : ℂ)),
    have h3 : g = (f ∘ λ (y : ℝ), (y : ℂ)) := rfl,
    rw [←h3],
    have h4 : ∫ (x : ℝ) in a..b, g x = ∫ (x : ℝ) in (b - a) * 0 + a..(b - a) * 1 + a, g x := by simp,
    rw h4,
    rw ←interval_integral.smul_integral_comp_mul_add g (b - a) a,
    have h5 : ∫ (x : ℝ) in 0..1, g ((b - a) * x + a) = ∫ (x : ℝ) in 0..1, g ((b - a) * x + a) := rfl,
    rw smul_type_convert (b-a) ∫ (x : ℝ) in 0..1, g ((b - a) * x + a),
  },
  {
    simp at hneq,
    rw hneq,
    simp,
  }
end 

lemma integral_along_horizontal_line (f:ℂ → E)(a:ℝ)(b:ℝ)(c:ℝ):
  contour_integral f (line_segment (a+c*complex.I) (b+c*complex.I)) = 
  ∫ (t: ℝ) in a..b, f(t+c*complex.I) :=
begin
  have hr: ∫ (t: ℝ) in a..b, f(t+c*complex.I) =
    ∫ (t: ℝ) in a..b, (f∘ (complex_affine 1 (c*complex.I))) t:=
    by {rw complex_affine,simp,},
  have hl: (line_segment (↑a + ↑c * complex.I) (↑b + ↑c * complex.I))
    = (complex_affine 1 (c*complex.I)) ∘ (line_segment a b) :=
    by {rw complex_affine, repeat {rw line_segment,}, 
        simp, ext1, simp, ring_nf,},
  rw hr, rw hl,
  rw contour_integral_under_affine _ _ _,
  rw integral_along_reals _ a b,
  simp,
end

lemma integral_along_vertical_line (f:ℂ → E)(a:ℝ)(b:ℝ)(c:ℝ):
  contour_integral f (line_segment (c+a*complex.I) (c+b*complex.I)) = 
  complex.I • ∫ (t: ℝ) in a..b, f(c+t*complex.I) :=
begin
  have hr: ((λ t:ℝ, f (↑c + ↑t * complex.I)):ℝ → E)
  = ((λt:ℝ, (f ∘ (complex_affine complex.I c)) t):ℝ→ E) := 
    by {rw complex_affine, simp, ext1, ring_nf,},
  have hl:(line_segment (↑c + ↑a * complex.I) (↑c + ↑b * complex.I))
    = (complex_affine complex.I c) ∘ (line_segment a b) :=
    by {repeat {rw complex_affine,}, repeat {rw line_segment,}, 
    simp, ext1, simp, ring_nf,},
  rw hr, rw hl,
  rw contour_integral_under_affine _ _ _,
  rw integral_along_reals _ a b,
end

-- lemma integral_along_rectangle

/-- Part IV. Formalize the Cauchy theorem on rectangles. -/

/- Part V. Formalize the Cauchy integral formula on rectangles. -/

/- Part VI. (perhaps irrelevant) Define circles. -/

def circle_loop(c : ℂ) (R : ℝ) : ℝ → ℂ := 
  λ θ, c + R * complex.exp (θ * 2 * real.pi* complex.I)

lemma circle_loop_in_lib(c : ℂ) (R : ℝ)(t:ℝ ): 
circle_loop c R t = circle_map c R (2*real.pi*t):=
begin
  rw circle_loop,
  rw circle_map,
  ext1,
  simp,
  left,
  ring_nf,
  simp,
  left,
  ring_nf,
end

lemma circle_loop_in_lib'(c : ℂ) (R : ℝ):
circle_loop c R = (circle_map c R) ∘ (affine_function (2*real.pi) 0):=
begin
  ext1,
  rw affine_function,
  simp,
  exact circle_loop_in_lib c R x,
end 
