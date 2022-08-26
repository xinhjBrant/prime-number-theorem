import contourintegral
import analysis.calculus.dslope
import analysis.complex.cauchy_integral
noncomputable theory

variables {E : Type} 
[normed_add_comm_group E] [normed_space ℂ E] [complete_space E] 

/-! Part I. Define line segments 

- # Line Segments
-/

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

lemma line_is_continuous_on (a:ℂ )(b:ℂ ):
  continuous_on (line_segment a b) (set.interval 0 1):=
  (line_is_continuous a b).continuous_on

lemma line_is_in_C1 (a:ℂ )(b:ℂ):
  continuous (deriv (line_segment a b)):=
begin
  rw deriv_of_line a b,
  exact continuity_of_constant_path (b-a),
end

lemma deriv_line_integrable (a:ℂ)(b:ℂ):
  interval_integrable (deriv (line_segment a b)) 
  measure_theory.measure_space.volume 0 1:=
continuous.interval_integrable (line_is_in_C1 a b) 0 1

/-! Part II. Define rectangles 

- # Rectangles
-/

def rec_bottom (l:ℝ)(b:ℝ)(r:ℝ):=
  line_segment (l+b*complex.I) (r+b*complex.I)
def rec_right (b:ℝ)(r:ℝ)(t:ℝ):=
  line_segment (r+b*complex.I) (r+t*complex.I)
def rec_top (r:ℝ)(t:ℝ)(l:ℝ):=
  line_segment (r+t*complex.I) (l+t*complex.I)
def rec_left (t:ℝ)(l:ℝ)(b:ℝ):=
  line_segment (l+t*complex.I) (l+b*complex.I)

@[protected] lemma bottom_join_right (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) : 
  rec_bottom l b r 1 = rec_right b r t 0:=
begin
  rw rec_bottom, rw rec_right, repeat {rw line_segment,}, 
  simp, ring_nf,
end 

def rec_bottomright (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) :=
  path_concatenation (bottom_join_right b r t l) 

@[protected] lemma top_join_left (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) : 
  rec_top r t l 1 = rec_left t l b 0:=
begin
  rw rec_top, rw rec_left, repeat {rw line_segment,}, 
  simp, ring_nf,
end 

def rec_topleft (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) :=
  path_concatenation (top_join_left b r t l) 

@[protected] lemma br_join_tl (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) :
  rec_bottomright b r t l 1 = rec_topleft b r t l 0 :=
begin
  rw [rec_bottomright, rec_topleft],
  rw path_concatenation_endpoint _,
  rw rec_right, rw path_concatenation, simp,
  rw rec_top, repeat {rw line_segment,}, simp, ring_nf,
end

def rectangle (b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ) := 
  path_concatenation (br_join_tl b r t l) 

lemma image_rec_bottom {l:ℝ}(b:ℝ){r:ℝ}(lr:l≤ r):
set.image (rec_bottom l b r) (set.interval 0 1)
⊆  {z:ℂ | l≤ z.re ∧ z.re≤ r ∧ z.im = b} :=
begin
  unfold rec_bottom, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  apply mul_nonneg,
  simp, exact lr, exact a_ge,
  have temp: (r-l)*a≤ r-l :=
    by {apply mul_nonneg_le_one_le, 
    simp, exact lr, exact rfl.ge, 
    exact a_ge, exact a_le,},
  have t:=add_le_add_right temp l,
  simp at t, exact t,
end

lemma image_rectangle_sub{b r t l:ℝ}(bt: b≤ t)(lr: l≤ r):
set.image (rectangle b r t l) (set.interval 0 1)
⊆ (set.interval l r ×ℂ set.interval b t) :=
begin
  sorry,
end

@[protected] lemma rec_bottomright_continuous_on(b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ):
continuous_on (rec_bottomright b r t l) (set.interval 0 1):=
path_concatenation_continuous_on 
(bottom_join_right b r t l)
(line_is_continuous_on (l+b*complex.I) (r+b*complex.I))
(line_is_continuous_on (r+b*complex.I) (r+t*complex.I))

@[protected] lemma rec_topleft_continuous_on(b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ):
continuous_on (rec_topleft b r t l) (set.interval 0 1):=
path_concatenation_continuous_on 
(top_join_left b r t l)
(line_is_continuous_on (r+t*complex.I) (l+t*complex.I))
(line_is_continuous_on (l+t*complex.I) (l+b*complex.I))

lemma rectangle_continuous_on(b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ):
continuous_on (rectangle b r t l) (set.interval 0 1):=
path_concatenation_continuous_on 
(br_join_tl b r t l)
(rec_bottomright_continuous_on b r t l)
(rec_topleft_continuous_on b r t l)

@[protected] lemma deriv_rec_bottomright_integrable(b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ):
interval_integrable (deriv (rec_bottomright b r t l))
measure_theory.measure_space.volume 0 1 :=
path_concatenation_deriv_integrable
(bottom_join_right b r t l)
(deriv_line_integrable (l+b*complex.I) (r+b*complex.I))
(deriv_line_integrable (r+b*complex.I) (r+t*complex.I))

@[protected] lemma deriv_rec_topleft_integrable(b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ):
interval_integrable (deriv (rec_topleft b r t l))
measure_theory.measure_space.volume 0 1 :=
path_concatenation_deriv_integrable
(top_join_left b r t l)
(deriv_line_integrable (r+t*complex.I) (l+t*complex.I))
(deriv_line_integrable (l+t*complex.I) (l+b*complex.I))

lemma deriv_rectangle_integrable(b:ℝ)(r:ℝ)(t:ℝ)(l:ℝ):
interval_integrable (deriv (rectangle b r t l))
measure_theory.measure_space.volume 0 1 :=
path_concatenation_deriv_integrable
(br_join_tl b r t l)
(deriv_rec_bottomright_integrable b r t l)
(deriv_rec_topleft_integrable b r t l)

/-! Part III. Define integrals along rectangles

- # Integral along Rectangles
-/

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

lemma integral_along_rectangle_bottom(f:ℂ → E)
(l:ℝ)(b:ℝ)(r:ℝ):
  contour_integral f (rec_bottom l b r) 
  = ∫ (x: ℝ) in l..r, f(x+b*complex.I) :=
  integral_along_horizontal_line f l r b

lemma integral_along_rectangle_right(f:ℂ → E)
(b:ℝ)(r:ℝ)(t:ℝ):
  contour_integral f (rec_right b r t) 
  = complex.I • ∫ (x: ℝ) in b..t, f(r+x*complex.I) :=
  integral_along_vertical_line f b t r

lemma integral_along_rectangle_top(f:ℂ → E)
(r:ℝ)(t:ℝ)(l:ℝ):
  contour_integral f (rec_top r t l) 
  = - ∫ (x: ℝ) in l..r, f(x+t*complex.I) :=
  by { unfold rec_top,
       rw integral_along_horizontal_line f r l t,
       rw interval_integral.integral_symm, }

lemma integral_along_rectangle_left(f:ℂ → E)
(t:ℝ)(l:ℝ)(b:ℝ):
  contour_integral f (rec_left t l b) 
  = - complex.I • ∫ (x: ℝ) in b..t, f(l+x*complex.I) :=
  by { unfold rec_left,
       rw integral_along_vertical_line f t b l,
       rw interval_integral.integral_symm, simp, }

@[protected] lemma integral_along_rectangle_bottomright' 
{f:ℂ → E}{b r t l: ℝ}
(hf: continuous_on f 
  (set.image (rec_bottomright b r t l) (set.interval 0 1))):
  contour_integral f (rec_bottomright b r t l)
  = (contour_integral f (rec_bottom l b r))
  + (contour_integral f (rec_right b r t)):=
contour_integral_along_piecewise_path' hf 
(rec_bottomright_continuous_on b r t l)
(deriv_rec_bottomright_integrable b r t l)

@[protected] lemma integral_along_rectangle_topleft' 
{f:ℂ → E}{b r t l: ℝ}
(hf: continuous_on f 
  (set.image (rec_topleft b r t l) (set.interval 0 1))):
  contour_integral f (rec_topleft b r t l)
  = (contour_integral f (rec_top r t l))
  + (contour_integral f (rec_left t l b)):=
contour_integral_along_piecewise_path' hf 
(rec_topleft_continuous_on b r t l)
(deriv_rec_topleft_integrable b r t l)

theorem integral_along_rectangle'
{f:ℂ → E}{b r t l: ℝ}
(hf: continuous_on f 
  (set.image (rectangle b r t l) (set.interval 0 1))):
  contour_integral f (rectangle b r t l)
  = (((contour_integral f (rec_bottom l b r))
  + (contour_integral f (rec_top r t l)))
  + (contour_integral f (rec_right b r t)))
  + (contour_integral f (rec_left t l b)) :=
begin
  unfold rectangle,
  rw contour_integral_along_piecewise_path' hf 
     (rectangle_continuous_on b r t l)
     (deriv_rectangle_integrable b r t l),
  have hfbr:=continuous_on.mono hf 
       (path_concatenation_image_left_subset (br_join_tl b r t l)),
  have hftl:=continuous_on.mono hf 
       (path_concatenation_image_right_subset (br_join_tl b r t l)),
  rw integral_along_rectangle_bottomright' hfbr,
  rw integral_along_rectangle_topleft' hftl,
  rw ← add_assoc (contour_integral f (rec_bottom l b r) + 
  contour_integral f (rec_right b r t)) _ _,
  rw add_assoc _ (contour_integral f (rec_right b r t)) 
  (contour_integral f (rec_top r t l) ),
  rw add_comm (contour_integral f (rec_right b r t)) 
  (contour_integral f (rec_top r t l) ),
  rw ← add_assoc (contour_integral f (rec_bottom l b r)) _ _,
end

@[simp] lemma addminus{a:E}{b:E}: a+(-b)=a - b:= 
by {have t: -b=0-b:= by simp, rw t,
    rw ← add_sub_assoc, simp,}

theorem integral_along_rectangle
{f:ℂ → E}{b r t l: ℝ}
(hf: continuous_on f 
  (set.image (rectangle b r t l) (set.interval 0 1))):
  contour_integral f (rectangle b r t l)
  = (((∫ (x: ℝ) in l..r, f(x+b*complex.I))
  - (∫ (x: ℝ) in l..r, f(x+t*complex.I)))
  + (complex.I • ∫ (x: ℝ) in b..t, f(r+x*complex.I)))
  - (complex.I • ∫ (x: ℝ) in b..t, f(l+x*complex.I)) :=
begin
  rw integral_along_rectangle' hf,
  rw integral_along_rectangle_bottom,
  rw integral_along_rectangle_top,
  rw integral_along_rectangle_right,
  rw integral_along_rectangle_left,
  simp,
end

/-! Part IV. Formalize the Cauchy theorem on rectangles. 

- # Cauchy Theorem on Rectangles
-/

theorem Cauchy_Goursat_rectangle {f : ℂ → E} (c: ℂ) 
{b r t l:ℝ}(bt: b≤ t)(lr: l≤ r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t)) 
(Hd : ∀ (x : ℂ), x ∈ (set.Ioo l r ×ℂ set.Ioo b t) \ {c} 
→ differentiable_at ℂ f x) :
contour_integral f (rectangle b r t l) = 0 :=
begin
  have hf: continuous_on f 
       (set.image (rectangle b r t l) (set.interval 0 1)):=
       continuous_on.mono Hc (image_rectangle_sub bt lr),
  rw integral_along_rectangle hf,
  let s:set ℂ:={c},
  have hs:s.countable:=set.to_countable s,
  let z:ℂ:={re:=l,im:=b},
  let w:ℂ:={re:=r,im:=t},
  have z_re : l = z.re := rfl,
  have w_re : r = w.re := rfl,
  have z_im : b = z.im := rfl,
  have w_im : t = w.im := rfl,
  have hl : l = linear_order.min z.re w.re := 
    by {rw [←z_re, ←w_re], symmetry, exact min_eq_left lr,},
  have hr : r = linear_order.max z.re w.re := 
    by {rw [←z_re, ←w_re], symmetry, exact max_eq_right lr,},
  have hb : b = linear_order.min z.im w.im := 
    by {rw [←z_im, ←w_im], symmetry, exact min_eq_left bt,},
  have ht : t = linear_order.max z.im w.im := 
    by {rw [←z_im, ←w_im], symmetry, exact max_eq_right bt,},
  rw [z_re, w_re, z_im, w_im] at Hc,
  rw [hl, hr, hb, ht] at Hd,
  have t:=complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable 
           f z w s hs Hc Hd,
  exact t,
end

/-! Part V. Formalize the Cauchy integral formula on rectangles. 

- # Cauchy Integral Formula on Rectangles
-/
lemma dslope_eq_on{f : ℂ → E}{c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.eq_on (dslope f c) (λz:ℂ, (z-c)⁻¹•f(z)- (z-c)⁻¹•f(c)) 
(set.image (rectangle b r t l) (set.interval 0 1)):=
begin
  sorry,
end

lemma dslope_continuous_on {f : ℂ → E}{c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
continuous_on (dslope f c) (set.interval l r ×ℂ set.interval b t):=
begin
  have c_in_Ioo_prod: c∈ (set.Ioo l r ×ℂ set.Ioo b t):=
    by sorry,
  have hs:(set.interval l r ×ℂ set.interval b t)∈ nhds c:=
    by sorry,
  rw continuous_on_dslope hs,
  split,
  exact Hc,
  sorry,
end

lemma dslope_differentiable_at {f : ℂ → E}{c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
∀ (x : ℂ), x ∈ set.Ioo l r ×ℂ set.Ioo b t \ {c} → 
differentiable_at ℂ (dslope f c) x :=
begin
  intros x x_in,
  have x_ne_c: x ≠ c:= by sorry,
  rw differentiable_at_dslope_of_ne x_ne_c,
  sorry,
end

lemma dslope_zero_integral {f : ℂ → E} {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
contour_integral (dslope f c) (rectangle b r t l) = 0 :=
begin
  have bt: b≤ t:= by sorry,
  have lr: l≤ r:= by sorry,
  apply Cauchy_Goursat_rectangle c bt lr,
  exact dslope_continuous_on bc ct lc cr Hc Hd,
  exact dslope_differentiable_at bc ct lc cr Hc Hd,
end

lemma Cauchy_integral_formula_rectangle_pre{f : ℂ → E} {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
contour_integral (λz:ℂ, (z-c)⁻¹•f(z)) (rectangle b r t l)=
contour_integral (λz:ℂ, (z-c)⁻¹•f(c)) (rectangle b r t l):=
begin
  sorry,
end

/-! Part VI. (perhaps irrelevant) Define circles. 

- # Circles
-/

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
