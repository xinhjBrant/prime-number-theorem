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

lemma center_in_interior_rectangle{c:ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
c ∈ (set.Ioo l r ×ℂ set.Ioo b t) :=
begin
  unfold set.re_prod_im,
  simp, split, split,
  exact lc, exact cr, split,
  exact bc, exact ct,
end

lemma center_in_interior_rectangle_iff {c:ℂ}
{b r t l:ℝ}: c ∈ (set.Ioo l r ×ℂ set.Ioo b t) ↔
((l < c.re ∧ c.re < r)∧ b < c.im ∧ c.im < t ) :=
begin
  split,
  intros c_in,
  unfold set.re_prod_im at c_in,
  simp at c_in, exact c_in,
  intros in_cond,
  exact center_in_interior_rectangle (in_cond.2.1) 
    (in_cond.2.2) (in_cond.1.1) (in_cond.1.2),
end

lemma point_in_closure_rectangle{c:ℂ}
{b r t l:ℝ}(bc: b ≤ c.im) (ct: c.im ≤ t)
(lc: l ≤ c.re) (cr: c.re ≤ r):
c ∈ (set.interval l r ×ℂ set.interval b t) :=
begin 
  have bt:b≤ t:= le_trans bc ct,
  have lr:l≤ r:= le_trans lc cr,
  unfold set.re_prod_im,
  simp, split, split,
  rw min_eq_left lr, exact lc,
  rw max_eq_right lr, exact cr,
  split, rw min_eq_left bt, exact bc,
  rw max_eq_right bt, exact ct, 
end

lemma interior_rectangle_open(b r t l:ℝ): 
is_open (set.Ioo l r ×ℂ set.Ioo b t) :=
begin
  apply is_open.re_prod_im,
  exact is_open_Ioo,
  exact is_open_Ioo,
end

lemma interior_rectangle_sub_closure(b r t l:ℝ):
(set.Ioo l r ×ℂ set.Ioo b t)⊆ 
(set.interval l r ×ℂ set.interval b t) :=
begin
  unfold set.re_prod_im,
  have lr : set.Ioo l r ⊆ set.interval l r := 
    Ioo_subset_interval,
  have bt : set.Ioo b t ⊆ set.interval b t := 
    Ioo_subset_interval, 
  intro, simp,
  intros ll rr bb tt, split,
  have x_re_in:x.re∈ set.Ioo l r := 
    by {unfold set.Ioo, simp, split, exact ll, exact rr,},
  exact lr x_re_in,
  have x_im_in:x.im∈ set.Ioo b t:=
    by {unfold set.Ioo, simp, split, exact bb, exact tt,},
  exact bt x_im_in,
end

lemma interior_rectangle_neighborhood {c: ℂ}
{b r t l:ℝ} (hin: c ∈ (set.Ioo l r ×ℂ set.Ioo b t)):
(set.Ioo l r ×ℂ set.Ioo b t) ∈ (nhds c) :=
begin
  rw mem_nhds_iff,
  use (set.Ioo l r ×ℂ set.Ioo b t),
  split, exact rfl.subset,
  split, exact interior_rectangle_open b r t l,
  exact hin,
end

lemma interior_rectangle_neighborhood' {c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
(set.Ioo l r ×ℂ set.Ioo b t) ∈ (nhds c) :=
begin
  exact interior_rectangle_neighborhood 
    (center_in_interior_rectangle bc ct lc cr),
end

lemma closure_rectangle_neighborhood {c: ℂ}
{b r t l:ℝ} (hin: c ∈ (set.Ioo l r ×ℂ set.Ioo b t) ):
(set.interval l r ×ℂ set.interval b t) ∈ (nhds c) :=
begin
  rw mem_nhds_iff,
  use (set.Ioo l r ×ℂ set.Ioo b t),
  split, exact interior_rectangle_sub_closure b r t l,
  split, exact interior_rectangle_open b r t l,
  exact hin,
end

lemma closure_rectangle_neighborhood' {c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
(set.interval l r ×ℂ set.interval b t) ∈ (nhds c) :=
begin
  exact closure_rectangle_neighborhood 
    (center_in_interior_rectangle bc ct lc cr),
end

lemma image_rec_bottom {l:ℝ}(b:ℝ){r:ℝ}(lr:l≤ r):
set.image (rec_bottom l b r) (set.interval 0 1)
⊆  {z:ℂ | l≤ z.re ∧ z.re≤ r ∧ z.im = b} :=
begin
  unfold rec_bottom, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    apply mul_nonneg,
    simp, exact lr, exact a_ge,
  },
  {
    have temp: (r-l)*a≤ r-l :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact lr, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp':=add_le_add_right temp l,
    simp at temp', exact temp',
  },
end

lemma image_rec_right {b:ℝ}(r:ℝ){t:ℝ}(bt:b≤ t):
set.image (rec_right b r t) (set.interval 0 1)
⊆  {z:ℂ | b≤ z.im ∧ z.im≤ t ∧ z.re = r} :=
begin
  unfold rec_right, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    apply mul_nonneg,
    simp, exact bt, exact a_ge,
  },
  {
    have temp: (t-b)*a≤ t-b :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact bt, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp':=add_le_add_right temp b,
    simp at temp', exact temp',
  },
end

lemma image_rec_top {r:ℝ}(t:ℝ){l:ℝ}(lr:l≤ r):
set.image (rec_top r t l) (set.interval 0 1)
⊆  {z:ℂ | l≤ z.re ∧ z.re≤ r ∧ z.im = t} :=
begin
  unfold rec_top, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    have temp: (r-l)*a≤ r-l :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact lr, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp_m: -(r-l)≤ -((r-l)*a):=neg_le_neg temp,
    have temp':=add_le_add_right temp_m r,
    have rwl : -(r - l) + r = l:= by ring_nf,
    have rwr : -((r - l) * a) + r = (l - r) * a + r :=by ring_nf,
    rw [rwl, rwr] at temp', exact temp',
  },
  {
    apply mul_nonpos_of_nonpos_of_nonneg,
    simp, exact lr, exact a_ge,
  },
end

lemma image_rec_left {t:ℝ}(l:ℝ){b:ℝ}(bt:b≤ t):
set.image (rec_left t l b) (set.interval 0 1)
⊆  {z:ℂ | b≤ z.im ∧ z.im≤ t ∧ z.re = l} :=
begin
  unfold rec_left, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    have temp: (t-b)*a≤ t-b :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact bt, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp_m: -(t-b)≤ -((t-b)*a):=neg_le_neg temp,
    have temp':=add_le_add_right temp_m t,
    have rwl : -(t - b) + t = b:= by ring_nf,
    have rwr : -((t - b) * a) + t = (b - t) * a + t :=by ring_nf,
    rw [rwl, rwr] at temp', exact temp',
  },
  {
    apply mul_nonpos_of_nonpos_of_nonneg,
    simp, exact bt, exact a_ge,
  },
end

lemma image_rectangle'{b r t l:ℝ}(bt: b≤ t)(lr: l≤ r):
set.image (rectangle b r t l) (set.interval 0 1)=
((set.image (rec_bottom l b r) (set.interval 0 1))∪ 
(set.image (rec_right b r t) (set.interval 0 1))) ∪ 
((set.image (rec_top r t l) (set.interval 0 1))∪
(set.image (rec_left t l b) (set.interval 0 1))):=
begin
  unfold rectangle,
  rw path_concatenation_image (br_join_tl b r t l),
  rw [rec_bottomright, rec_topleft],
  rw path_concatenation_image (bottom_join_right b r t l),
  rw path_concatenation_image (top_join_left b r t l),
end

lemma image_rectangle_sub_closure{b r t l:ℝ}
(bt: b≤ t)(lr: l≤ r):
set.image (rectangle b r t l) (set.interval 0 1)
⊆ (set.interval l r ×ℂ set.interval b t) :=
begin
  rw image_rectangle' bt lr,
  apply set.union_subset,
  apply set.union_subset,
  {
    intros x x_in,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_bottom b lr) x_in, 
    simp at x_in', 
    apply point_in_closure_rectangle,
    exact eq.ge x_in'.2.2,
    rw x_in'.2.2, exact bt,
    exact x_in'.1, exact x_in'.2.1,
  },
  {
    intros x x_in,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_right r bt) x_in, 
    simp at x_in', 
    apply point_in_closure_rectangle,
    exact x_in'.1, exact x_in'.2.1,
    rw x_in'.2.2, exact lr,
    exact (eq.symm x_in'.2.2).ge,
  },
  apply set.union_subset,
  {
    intros x x_in,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_top t lr) x_in, 
    simp at x_in', 
    apply point_in_closure_rectangle,
    rw x_in'.2.2, exact bt,
    exact (eq.symm x_in'.2.2).ge,
    exact x_in'.1, exact x_in'.2.1,
  },
  {
    intros x x_in,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_left l bt) x_in, 
    simp at x_in', 
    apply point_in_closure_rectangle,
    exact x_in'.1, exact x_in'.2.1,
    exact eq.ge x_in'.2.2,
    rw x_in'.2.2, exact lr,
  },
end

lemma image_rectangle_sub_compl_center{c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.image (rectangle b r t l) (set.interval 0 1) ⊆ {c}ᶜ :=
begin
  have b_lt_t : b<t := lt_trans bc ct,
  have l_lt_r : l<r := lt_trans lc cr,
  have bt: b≤ t:= le_of_lt b_lt_t,
  have lr: l≤ r:= le_of_lt l_lt_r,
  rw image_rectangle' bt lr,
  rw set.union_subset_iff, split,
  rw set.union_subset_iff, split,
  {
    intros x x_in, simp, intro x_c,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_bottom b lr) x_in, 
    simp at x_in', rw x_c at x_in',
    rw x_in'.2.2 at bc, simp at bc, exact bc,
  },
  {
    intros x x_in, simp, intro x_c,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_right r bt) x_in, 
    simp at x_in', rw x_c at x_in',
    rw x_in'.2.2 at cr, simp at cr, exact cr,
  },
  rw set.union_subset_iff, split,
  {
    intros x x_in, simp, intro x_c,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_top t lr) x_in, 
    simp at x_in', rw x_c at x_in',
    rw x_in'.2.2 at ct, simp at ct, exact ct,
  },
  {
    intros x x_in, simp, intro x_c,
    have x_in':=set.mem_of_subset_of_mem 
      (image_rec_left l bt) x_in, 
    simp at x_in', rw x_c at x_in',
    rw x_in'.2.2 at lc, simp at lc, exact lc,
  },
end

lemma image_rectangle_sub_closure_inter_compl_center
{c: ℂ}{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.image (rectangle b r t l) (set.interval 0 1) ⊆ 
(set.interval l r ×ℂ set.interval b t) ∩ {c}ᶜ :=
begin
  have b_lt_t : b<t := lt_trans bc ct,
  have l_lt_r : l<r := lt_trans lc cr,
  have bt: b≤ t:= le_of_lt b_lt_t,
  have lr: l≤ r:= le_of_lt l_lt_r,
  rw set.subset_inter_iff, split,
  exact image_rectangle_sub_closure bt lr,
  exact image_rectangle_sub_compl_center bc ct lc cr,
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
       continuous_on.mono Hc (image_rectangle_sub_closure bt lr),
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

lemma zero_exact{a b:E}(h:0=a-b):a=b:=
begin
  have b_z: b=b+0:= by simp,
  rw h at b_z,
  rw b_z, simp,
end

lemma dslope_eq_on{f : ℂ → E}{c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.eq_on (dslope f c) (λz:ℂ, (z-c)⁻¹•f(z) - (z-c)⁻¹•f(c)) 
(set.image (rectangle b r t l) (set.interval 0 1)):=
begin
  apply set.eq_on.mono 
    (image_rectangle_sub_compl_center bc ct lc cr),
  have func_eq:(λz:ℂ, (z-c)⁻¹•f(z) - (z-c)⁻¹•f(c))=
    slope f c := 
    by {ext1, rw slope_def_module f c x, rw smul_sub,},
  rw func_eq,
  exact eq_on_dslope_slope f c,
end

lemma dslope_continuous_on {f : ℂ → E}{c: ℂ}
{b r t l:ℝ}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
continuous_on (dslope f c) (set.interval l r ×ℂ set.interval b t):=
begin
  rw continuous_on_dslope 
    (closure_rectangle_neighborhood' bc ct lc cr),
  split,
  exact Hc,
  exact differentiable_on.differentiable_at Hd 
    (interior_rectangle_neighborhood' bc ct lc cr),
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
  simp at x_in,
  rw differentiable_at_dslope_of_ne x_in.2,
  have hd:=Hd x x_in.1,
  exact differentiable_within_at.differentiable_at hd
    (interior_rectangle_neighborhood x_in.1),
end

lemma dslope_zero_integral {f : ℂ → E} {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
contour_integral (dslope f c) (rectangle b r t l) = 0 :=
begin
  have b_lt_t : b<t := lt_trans bc ct,
  have l_lt_r : l<r := lt_trans lc cr,
  have bt: b≤ t:= le_of_lt b_lt_t,
  have lr: l≤ r:= le_of_lt l_lt_r,
  apply Cauchy_Goursat_rectangle c bt lr,
  exact dslope_continuous_on bc ct lc cr Hc Hd,
  exact dslope_differentiable_at bc ct lc cr Hc Hd,
end

lemma reciprocal_continuous (c: ℂ) :
continuous_on (λ (z : ℂ), (z - c)⁻¹) {c}ᶜ :=
begin
  rw continuous_on,
  intros x x_in, 
  simp at x_in,
  apply continuous_at.continuous_within_at,
  have func_eq: (λ (z : ℂ), (z - c)⁻¹)
  =(λ (z:ℂ), z⁻¹) ∘ (λ (z : ℂ), (z - c)) :=
    by {ext1, simp,},
  rw func_eq,
  apply continuous_at.comp,
  have h: (x-c)≠ 0 := by {symmetry, intro hy, 
    have h':=zero_exact hy, exact x_in h',},
  exact normed_field.continuous_at_inv.mpr h,
  have cm: continuous (λ (z : ℂ), z - c) :=
    continuous_sub_right c,
  exact continuous.continuous_at cm,
end

lemma part_of_dslope_continuous{f : ℂ → E} {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t)):
continuous_on ((λ (z : ℂ), (z - c)⁻¹) • f) 
(rectangle b r t l '' set.interval 0 1) :=
begin 
  have hr: continuous_on (λ (z : ℂ), (z - c)⁻¹) 
    (rectangle b r t l '' set.interval 0 1) := 
    continuous_on.mono (reciprocal_continuous c)
      (image_rectangle_sub_compl_center bc ct lc cr),
  have ss :(set.interval l r ×ℂ set.interval b t) ∩ {c}ᶜ
  ⊆ (set.interval l r ×ℂ set.interval b t) := 
  (set.interval l r ×ℂ set.interval b t).inter_subset_left {c}ᶜ,
  have hf': continuous_on f 
    ((set.interval l r ×ℂ set.interval b t) ∩ {c}ᶜ) :=
    continuous_on.mono Hc ss,
  have hf: continuous_on f 
    (rectangle b r t l '' set.interval 0 1) :=
    continuous_on.mono hf'
    (image_rectangle_sub_closure_inter_compl_center bc ct lc cr),
  have rf:= continuous_on.prod_map hr hf,
  exact continuous_on.smul hr hf,
end

lemma Cauchy_integral_formula_rectangle_pre{f : ℂ → E} {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
contour_integral (λz:ℂ, (z-c)⁻¹•f(z)) (rectangle b r t l)=
contour_integral (λz:ℂ, (z-c)⁻¹) (rectangle b r t l) • f(c):=
begin
  rw ← contour_integral_smul_right _ _ (f(c)),
  have func_eq:(λz:ℂ, (z-c)⁻¹•f(z) - (z-c)⁻¹•f(c))=
  (λz:ℂ, (z-c)⁻¹•f(z))-(λz:ℂ, (z-c)⁻¹•f(c)):=
    by {ext1, simp,},
  have left_func:(λ (z : ℂ), (z - c)⁻¹ • f z) =
  (λ (z : ℂ), (z - c)⁻¹) • f:=
    by {ext1, simp,},
  have right_func:(λ (z : ℂ), (z - c)⁻¹ • f c) =
  (λ (z : ℂ), (z - c)⁻¹) • (λ (z:ℂ), f c) :=
    by {ext1, simp,},
  have int_z:=dslope_zero_integral bc ct lc cr Hc Hd,
  rw contour_integral_congr (dslope_eq_on bc ct lc cr) at int_z,
  rw func_eq at int_z,
  have int_sub:contour_integral ((λ (z : ℂ), (z - c)⁻¹ • f z) - 
  λ (z : ℂ), (z - c)⁻¹ • f c) (rectangle b r t l) = 
  contour_integral (λ (z : ℂ), (z - c)⁻¹ • f z) (rectangle b r t l) - 
  contour_integral (λ (z : ℂ), (z - c)⁻¹ • f c) (rectangle b r t l):=
    begin
      apply contour_integral_sub',
      {
        rw left_func,
        exact part_of_dslope_continuous bc ct lc cr Hc,
      },
      {
        rw right_func,
        apply part_of_dslope_continuous bc ct lc cr,
        apply continuous.continuous_on,
        exact continuous_const,
        exact _inst_3,
      },
      {
        exact rectangle_continuous_on b r t l,
      },
      {
        exact deriv_rectangle_integrable b r t l,
      },
    end,
  rw int_z at int_sub, 
  exact zero_exact int_sub,
  exact _inst_3,
end

lemma winding_number_of_rectangle {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
contour_integral (λz:ℂ, (z-c)⁻¹) (rectangle b r t l)
= 2 * real.pi *complex.I :=
begin
  sorry,
end

theorem Cauchy_integral_formula_rectangle{f : ℂ → E} {c: ℂ}
{b r t l:ℝ} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r ×ℂ set.interval b t))
(Hd : differentiable_on ℂ f (set.Ioo l r ×ℂ set.Ioo b t)):
contour_integral (λz:ℂ, (z-c)⁻¹•f(z)) (rectangle b r t l)=
(2 * real.pi *complex.I :ℂ) • f(c) :=
begin
  rw Cauchy_integral_formula_rectangle_pre bc ct lc cr Hc Hd,
  rw winding_number_of_rectangle bc ct lc cr,
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
