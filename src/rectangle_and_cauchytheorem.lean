import contourintegral
import analysis.calculus.dslope
import analysis.complex.cauchy_integral
noncomputable theory

section tactic 

variables {E : Type} {ð: Type} [nontrivially_normed_field ð]
[normed_add_comm_group E] [normed_space ð E] [complete_space E] 

/-! Part O. tactic

- # Tactic
-/

@[simp] lemma addminus{a:E}{b:E}: a+(-b)=a - b:= 
by {have t: -b=0-b:= by simp, rw t,
    rw â add_sub_assoc, simp,}

lemma zero_exact{a b:E}(h:0=a-b):a=b:=
begin
  have b_z: b=b+0:= by simp,
  rw h at b_z,
  rw b_z, simp,
end

lemma zero_symm_exact{a b:E}(h:a-b=0):a=b:=
begin
  have h':0=a-b:=by rw h,
  exact zero_exact h',
end

lemma neg_rewrite {a b:E}: -a=b â a=-b := 
by {split, intro f, rwâ f,simp,
    intro f, rw f,simp,}

end tactic 

variables {E : Type} 
[normed_add_comm_group E] [normed_space â E] [complete_space E] 

/-! Part O'. basic function 

- # Basic Function
-/
/-- The derivative of the inclusion â â â is 1. --/
lemma coe_has_deriv (x:â ):
has_deriv_at (Î» (t : â), (t : â)) 1 x :=
begin
  rw has_deriv_at,
  rw has_deriv_at_filter_iff_is_o,
  simp,
end

lemma coe_differentiable: 
differentiable â (Î» (t : â), (t : â)):=
begin
  intro x,
  exact has_deriv_at.differentiable_at 
    (coe_has_deriv x),
end

lemma deriv_of_coe: deriv (Î» (x : â), (x : â)) = 1 :=
 deriv_eq coe_has_deriv

lemma complex_affine_has_deriv (a b x:â):
has_deriv_at (Î» (z : â), a * z + b) a x :=
begin
  apply has_deriv_at.add_const _ b,
  have frw:(Î» (x : â), a * x)=(Î» (x : â), x * a):=
    by {ext1,rw mul_comm,}, rw frw,
  exact has_deriv_at_mul_const a,
end

lemma complex_affine_differentiable(a b:â):
differentiable â (Î» (z : â), a * z + b):=
begin
  intro x,
  exact has_deriv_at.differentiable_at 
    (complex_affine_has_deriv a b x),
end

lemma affine_rtc_has_deriv(a b :â)(x:â):
has_deriv_at ((Î» x:â, a*x+b):ââ â) a x:=
begin
  have func_eq:((Î» x:â, a*x+b):ââ â)= 
    ((Î» z:â, a*z+b):ââ â) â (Î» (t : â), (t : â)) :=
    by {ext1, simp,},
  have conc: has_deriv_at ((Î» (z : â), a * z + b) 
    â Î» (t : â), ât) a x â has_deriv_at ((Î» (z : â), 
    a * z + b) â Î» (t : â), ât) (a*1) x:= by simp,
  rw [func_eq, conc],
  apply has_deriv_at.comp,
  exact complex_affine_has_deriv a b _,
  exact coe_has_deriv _,
end

lemma affine_rtc_differentiable(a b:â):
differentiable â ((Î» x:â, a*x+b):ââ â):=
begin
  intro x,
  exact has_deriv_at.differentiable_at 
    (affine_rtc_has_deriv a b x),
end

lemma affine_rtc_continuous (a b:â):
continuous ((Î» x:â, a*x+b):ââ â):=
differentiable.continuous (affine_rtc_differentiable a b)

lemma complex_affine_inverse_has_deriv{a b x:â}
(h: a*x+bâ  0):
has_deriv_at ((Î»(t:â), (a*t + b)â»Â¹):ââ â) 
(-a/(a*x+b)^2) x :=
has_deriv_at.inv (complex_affine_has_deriv a b x) h

lemma affine_rtc_inverse_has_deriv{a b :â}{x:â}
(h: a*x+bâ  0):
has_deriv_at ((Î»(t:â), (a*t + b)â»Â¹):ââ â) 
(-a/(a*x+b)^2) x :=
begin
  have func_rw:((Î»(t:â), (a*t + b)â»Â¹):ââ â)=
    ((Î»(t:â), (a*t + b)â»Â¹):ââ â) â (Î» (t : â), (t : â)):=
    by {ext1, simp,},
  have q:(-a/(a*x+b)^2) =(-a/(a*x+b)^2)*1:= by ring_nf,
  rw [func_rw,q],
  apply has_deriv_at.comp,
  exact complex_affine_inverse_has_deriv h,
  exact coe_has_deriv _,
end

lemma affine_rtc_differentiable_on{a b :â}{s: set â}
(h: â(x:â), xâ s â a*x+bâ  0):
differentiable_on â ((Î»(t:â), (a*t + b)â»Â¹):ââ â) s :=
begin
  intros x x_in,
  apply differentiable_at.differentiable_within_at,
  have x_in':= h x x_in,
  exact has_deriv_at.differentiable_at 
    (affine_rtc_inverse_has_deriv x_in'),
end

lemma affine_rtc_continuous_on{a b :â}{s: set â}
(h: â(x:â), xâ s â a*x+bâ  0):
continuous_on ((Î»(t:â), (a*t + b)â»Â¹):ââ â) s :=
differentiable_on.continuous_on 
  (affine_rtc_differentiable_on h)

lemma reciprocal_differentiable_on (c:â):
differentiable_on â (Î» (z : â), (z - c)â»Â¹) {c}á¶ :=
begin
  apply differentiable_on.inv,
  apply differentiable.differentiable_on,
  simp,
  intros x x_in, simp at x_in, symmetry,
  intro f, have h:=zero_exact f,
  exact x_in h,
end

lemma reciprocal_continuous_on (c:â) :
continuous_on (Î» (z : â), (z - c)â»Â¹) {c}á¶ :=
differentiable_on.continuous_on 
  (reciprocal_differentiable_on c)

/-! Part I. Define line segments 

- # Line Segments
-/

def line_segment (a:â) (b:â) : â â â :=
  Î» (Î¸ : â) , (b-a) * Î¸ + a

/-- The line sgement and circle are both continuously differentiable. --/
lemma deriv_of_line (a:â)(b:â): 
  deriv (line_segment a b)  = constant_path (b-a):=
begin
  unfold line_segment constant_path,
  ext1,
  simp,
  rw deriv_of_coe,
  simp,
end

lemma deriv_of_line' (a:â)(b:â)(x : â): 
  has_deriv_at (line_segment a b) (constant_path (b-a) x) x:=
begin
  unfold line_segment,
  have h0 : b - a = (b - a) + 0 := by simp,
  rw h0,
  apply has_deriv_at.add,
  have h2 : b - a = (1 : â) â¢ (b - a : â) := by simp,
  rw h2,
  have h1 : (Î» (x : â), ((1 : â) â¢ (b - a) + 0) * âx) = (Î» (x : â), (b - a + 0) * x) â (Î» (x : â), (x : â)) := by simp,
  rw h1,
  apply has_deriv_at.scomp,
  {
    rw has_deriv_at,
    rw has_deriv_at_filter_iff_is_o,
    simp,
    have mid: (Î» (x' : â), (b - a) * x' - 
      (b - a) * âx - (x' - âx) * (b - a)) = 
      (Î»(x:â), (0:â)) := by ring_nf,
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

lemma line_is_differentiable (a:â)(b:â): 
  differentiable â (line_segment a b):= 
begin
  unfold differentiable,
  intro x,
  apply has_deriv_at.differentiable_at (deriv_of_line' a b x),
end

lemma line_is_continuous (a:â )(b:â ):
  continuous (line_segment a b):=
  by {exact differentiable.continuous (line_is_differentiable a b),}

lemma line_is_continuous_on (a:â )(b:â ):
  continuous_on (line_segment a b) (set.interval 0 1):=
  (line_is_continuous a b).continuous_on

lemma line_is_in_C1 (a:â )(b:â):
  continuous (deriv (line_segment a b)):=
begin
  rw deriv_of_line a b,
  exact continuity_of_constant_path (b-a),
end

lemma deriv_line_integrable (a:â)(b:â):
  interval_integrable (deriv (line_segment a b)) 
  measure_theory.measure_space.volume 0 1:=
continuous.interval_integrable (line_is_in_C1 a b) 0 1

lemma line_integral_ML_inequality{f:â â E}{a b:â}{M:â}
(hf: â z:â, z â set.image (line_segment a b) 
(set.interval 0 1) â â¥f zâ¥ â¤ M):
â¥contour_integral f (line_segment a b)â¥ â¤ 
M * complex.abs(b-a) :=
begin
  apply contour_integral_ML_inequality,
  {
    intros z z_in,
    exact hf z ((set.image_subset (line_segment a b) 
      set.Ioc_subset_Icc_self) z_in),
  },
  {
    intros x _,
    rw deriv_of_line,
    unfold constant_path,
  },
end 

/-! Part II. Define rectangles 

- # Rectangles
-/

def rec_bottom (l:â)(b:â)(r:â):=
  line_segment (l+b*complex.I) (r+b*complex.I)
def rec_right (b:â)(r:â)(t:â):=
  line_segment (r+b*complex.I) (r+t*complex.I)
def rec_top (r:â)(t:â)(l:â):=
  line_segment (r+t*complex.I) (l+t*complex.I)
def rec_left (t:â)(l:â)(b:â):=
  line_segment (l+t*complex.I) (l+b*complex.I)

@[protected] lemma bottom_join_right (b:â)(r:â)(t:â)(l:â) : 
  rec_bottom l b r 1 = rec_right b r t 0:=
begin
  rw rec_bottom, rw rec_right, repeat {rw line_segment,}, 
  simp, ring_nf,
end 

def rec_bottomright (b:â)(r:â)(t:â)(l:â) :=
  path_concatenation (bottom_join_right b r t l) 

@[protected] lemma top_join_left (b:â)(r:â)(t:â)(l:â) : 
  rec_top r t l 1 = rec_left t l b 0:=
begin
  rw rec_top, rw rec_left, repeat {rw line_segment,}, 
  simp, ring_nf,
end 

def rec_topleft (b:â)(r:â)(t:â)(l:â) :=
  path_concatenation (top_join_left b r t l) 

@[protected] lemma br_join_tl (b:â)(r:â)(t:â)(l:â) :
  rec_bottomright b r t l 1 = rec_topleft b r t l 0 :=
begin
  rw [rec_bottomright, rec_topleft],
  rw path_concatenation_endpoint _,
  rw rec_right, rw path_concatenation, simp,
  rw rec_top, repeat {rw line_segment,}, simp, ring_nf,
end

def rectangle (b:â)(r:â)(t:â)(l:â) := 
  path_concatenation (br_join_tl b r t l) 

lemma center_in_interior_rectangle{c:â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
c â (set.Ioo l r Ãâ set.Ioo b t) :=
begin
  unfold set.re_prod_im,
  simp, split, split,
  exact lc, exact cr, split,
  exact bc, exact ct,
end

lemma center_in_interior_rectangle_iff {c:â}
{b r t l:â}: c â (set.Ioo l r Ãâ set.Ioo b t) â
((l < c.re â§ c.re < r)â§ b < c.im â§ c.im < t ) :=
begin
  split,
  intros c_in,
  unfold set.re_prod_im at c_in,
  simp at c_in, exact c_in,
  intros in_cond,
  exact center_in_interior_rectangle (in_cond.2.1) 
    (in_cond.2.2) (in_cond.1.1) (in_cond.1.2),
end

lemma point_in_closure_rectangle{c:â}
{b r t l:â}(bc: b â¤ c.im) (ct: c.im â¤ t)
(lc: l â¤ c.re) (cr: c.re â¤ r):
c â (set.interval l r Ãâ set.interval b t) :=
begin 
  have bt:bâ¤ t:= le_trans bc ct,
  have lr:lâ¤ r:= le_trans lc cr,
  unfold set.re_prod_im,
  simp, split, split,
  rw min_eq_left lr, exact lc,
  rw max_eq_right lr, exact cr,
  split, rw min_eq_left bt, exact bc,
  rw max_eq_right bt, exact ct, 
end

lemma interior_rectangle_open(b r t l:â): 
is_open (set.Ioo l r Ãâ set.Ioo b t) :=
is_open.re_prod_im is_open_Ioo is_open_Ioo

lemma interior_rectangle_sub_closure(b r t l:â):
(set.Ioo l r Ãâ set.Ioo b t)â 
(set.interval l r Ãâ set.interval b t) :=
begin
  unfold set.re_prod_im,
  have lr : set.Ioo l r â set.interval l r := 
    Ioo_subset_interval,
  have bt : set.Ioo b t â set.interval b t := 
    Ioo_subset_interval, 
  intro, simp,
  intros ll rr bb tt, split,
  have x_re_in:x.reâ set.Ioo l r := 
    by {unfold set.Ioo, simp, split, exact ll, exact rr,},
  exact lr x_re_in,
  have x_im_in:x.imâ set.Ioo b t:=
    by {unfold set.Ioo, simp, split, exact bb, exact tt,},
  exact bt x_im_in,
end

lemma interior_rectangle_neighborhood {c: â}
{b r t l:â} (hin: c â (set.Ioo l r Ãâ set.Ioo b t)):
(set.Ioo l r Ãâ set.Ioo b t) â (nhds c) :=
begin
  rw mem_nhds_iff,
  use (set.Ioo l r Ãâ set.Ioo b t),
  split, exact rfl.subset,
  split, exact interior_rectangle_open b r t l,
  exact hin,
end

lemma interior_rectangle_neighborhood' {c: â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
(set.Ioo l r Ãâ set.Ioo b t) â (nhds c) :=
  interior_rectangle_neighborhood 
  (center_in_interior_rectangle bc ct lc cr)

lemma closure_rectangle_neighborhood {c: â}
{b r t l:â} (hin: c â (set.Ioo l r Ãâ set.Ioo b t) ):
(set.interval l r Ãâ set.interval b t) â (nhds c) :=
begin
  rw mem_nhds_iff,
  use (set.Ioo l r Ãâ set.Ioo b t),
  split, exact interior_rectangle_sub_closure b r t l,
  split, exact interior_rectangle_open b r t l,
  exact hin,
end

lemma closure_rectangle_neighborhood' {c: â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
(set.interval l r Ãâ set.interval b t) â (nhds c) :=
  closure_rectangle_neighborhood 
  (center_in_interior_rectangle bc ct lc cr)

lemma image_rec_bottom {l:â}(b:â){r:â}(lr:lâ¤ r):
set.image (rec_bottom l b r) (set.interval 0 1)
â  {z:â | lâ¤ z.re â§ z.reâ¤ r â§ z.im = b} :=
begin
  unfold rec_bottom, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    apply mul_nonneg,
    simp, exact lr, exact a_ge,
  },
  {
    have temp: (r-l)*aâ¤ r-l :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact lr, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp':=add_le_add_right temp l,
    simp at temp', exact temp',
  },
end

lemma image_rec_right {b:â}(r:â){t:â}(bt:bâ¤ t):
set.image (rec_right b r t) (set.interval 0 1)
â  {z:â | bâ¤ z.im â§ z.imâ¤ t â§ z.re = r} :=
begin
  unfold rec_right, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    apply mul_nonneg,
    simp, exact bt, exact a_ge,
  },
  {
    have temp: (t-b)*aâ¤ t-b :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact bt, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp':=add_le_add_right temp b,
    simp at temp', exact temp',
  },
end

lemma image_rec_top {r:â}(t:â){l:â}(lr:lâ¤ r):
set.image (rec_top r t l) (set.interval 0 1)
â  {z:â | lâ¤ z.re â§ z.reâ¤ r â§ z.im = t} :=
begin
  unfold rec_top, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    have temp: (r-l)*aâ¤ r-l :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact lr, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp_m: -(r-l)â¤ -((r-l)*a):=neg_le_neg temp,
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

lemma image_rec_left {t:â}(l:â){b:â}(bt:bâ¤ t):
set.image (rec_left t l b) (set.interval 0 1)
â  {z:â | bâ¤ z.im â§ z.imâ¤ t â§ z.re = l} :=
begin
  unfold rec_left, unfold line_segment, 
  simp, unfold set.Icc, simp,
  intros a a_ge a_le, split, 
  {
    have temp: (t-b)*aâ¤ t-b :=
      by {apply mul_nonneg_le_one_le, 
      simp, exact bt, exact rfl.ge, 
      exact a_ge, exact a_le,},
    have temp_m: -(t-b)â¤ -((t-b)*a):=neg_le_neg temp,
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

lemma image_rectangle'{b r t l:â}(bt: bâ¤ t)(lr: lâ¤ r):
set.image (rectangle b r t l) (set.interval 0 1)=
((set.image (rec_bottom l b r) (set.interval 0 1))âª 
(set.image (rec_right b r t) (set.interval 0 1))) âª 
((set.image (rec_top r t l) (set.interval 0 1))âª
(set.image (rec_left t l b) (set.interval 0 1))):=
begin
  unfold rectangle,
  rw path_concatenation_image (br_join_tl b r t l),
  rw [rec_bottomright, rec_topleft],
  rw path_concatenation_image (bottom_join_right b r t l),
  rw path_concatenation_image (top_join_left b r t l),
end

lemma image_rectangle_sub_closure{b r t l:â}
(bt: bâ¤ t)(lr: lâ¤ r):
set.image (rectangle b r t l) (set.interval 0 1)
â (set.interval l r Ãâ set.interval b t) :=
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

lemma image_rectangle_sub_compl_center{c: â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.image (rectangle b r t l) (set.interval 0 1) â {c}á¶ :=
begin
  have bt: bâ¤ t:= le_of_lt (lt_trans bc ct),
  have lr: lâ¤ r:= le_of_lt (lt_trans lc cr),
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
{c: â}{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.image (rectangle b r t l) (set.interval 0 1) â 
(set.interval l r Ãâ set.interval b t) â© {c}á¶ :=
begin
  rw set.subset_inter_iff, split,
  exact image_rectangle_sub_closure 
    (le_of_lt (lt_trans bc ct)) (le_of_lt (lt_trans lc cr)),
  exact image_rectangle_sub_compl_center bc ct lc cr,
end

@[protected] lemma rec_bottomright_continuous_on(b:â)(r:â)(t:â)(l:â):
continuous_on (rec_bottomright b r t l) (set.interval 0 1):=
path_concatenation_continuous_on 
(bottom_join_right b r t l)
(line_is_continuous_on (l+b*complex.I) (r+b*complex.I))
(line_is_continuous_on (r+b*complex.I) (r+t*complex.I))

@[protected] lemma rec_topleft_continuous_on(b:â)(r:â)(t:â)(l:â):
continuous_on (rec_topleft b r t l) (set.interval 0 1):=
path_concatenation_continuous_on 
(top_join_left b r t l)
(line_is_continuous_on (r+t*complex.I) (l+t*complex.I))
(line_is_continuous_on (l+t*complex.I) (l+b*complex.I))

lemma rectangle_continuous_on(b:â)(r:â)(t:â)(l:â):
continuous_on (rectangle b r t l) (set.interval 0 1):=
path_concatenation_continuous_on 
(br_join_tl b r t l)
(rec_bottomright_continuous_on b r t l)
(rec_topleft_continuous_on b r t l)

@[protected] lemma deriv_rec_bottomright_integrable(b:â)(r:â)(t:â)(l:â):
interval_integrable (deriv (rec_bottomright b r t l))
measure_theory.measure_space.volume 0 1 :=
path_concatenation_deriv_integrable
(bottom_join_right b r t l)
(deriv_line_integrable (l+b*complex.I) (r+b*complex.I))
(deriv_line_integrable (r+b*complex.I) (r+t*complex.I))

@[protected] lemma deriv_rec_topleft_integrable(b:â)(r:â)(t:â)(l:â):
interval_integrable (deriv (rec_topleft b r t l))
measure_theory.measure_space.volume 0 1 :=
path_concatenation_deriv_integrable
(top_join_left b r t l)
(deriv_line_integrable (r+t*complex.I) (l+t*complex.I))
(deriv_line_integrable (l+t*complex.I) (l+b*complex.I))

lemma deriv_rectangle_integrable(b:â)(r:â)(t:â)(l:â):
interval_integrable (deriv (rectangle b r t l))
measure_theory.measure_space.volume 0 1 :=
path_concatenation_deriv_integrable
(br_join_tl b r t l)
(deriv_rec_bottomright_integrable b r t l)
(deriv_rec_topleft_integrable b r t l)

/-! Part III. Define integrals along rectangles

- # Integral along Rectangles
-/

def complex_affine (Î±:â)(c:â):ââ â:=Î»z, Î±*z+c

lemma contour_integral_under_affine (f:â â E)
(L:â â â)(Î±:â)(c:â):
  contour_integral f ((complex_affine Î± c)â L) = 
  Î± â¢ contour_integral (f â (complex_affine Î± c)) L :=
begin
  repeat {rw contour_integral},
  rw complex_affine,
  simp,
  rw smul_integral_convert,
  have l1: (Î» t:â, (Î± * deriv L t) â¢ f (Î± * L t + c))
    = (Î» t:â, Î± â¢  deriv L t â¢ f (Î± * L t + c)) :=
    by {ext1, rw smul_assoc_convert,},
  rw l1,
end

/- The contour integral along the sgements with both endpoints being real numbers is equal to the corresponding real integral. -/
lemma integral_along_reals (f:â â E)(a:â)(b:â):
  contour_integral f (line_segment a b) = 
  â« (t: â ) in a..b, f(t):=
begin
  unfold contour_integral,
  rw [deriv_of_line, constant_path, line_segment],
  simp,
  have h0 : â(b - a) = (b : â) - (a : â) := by simp,
  rw âh0,
  cases decidable.em (b â  a) with heq hneq,
  {
    have h1 : (Î» (x : â), f (â(b - a) * (x : â) + (a : â))) = (Î» (x : â), ((f â Î» (y : â), (y : â)) ((b - a) * x + a))) := by simp,
    have h2 : (Î» (t : â), f (t : â)) = (Î» (x : â), ((f â Î» (y : â), (y : â)) x)) := by simp,
    rw [h1, h2],
    let g := (f â Î» (y : â), (y : â)),
    have h3 : g = (f â Î» (y : â), (y : â)) := rfl,
    rw [âh3],
    have h4 : â« (x : â) in a..b, g x = â« (x : â) in (b - a) * 0 + a..(b - a) * 1 + a, g x := by simp,
    rw h4,
    rw âinterval_integral.smul_integral_comp_mul_add g (b - a) a,
    have h5 : â« (x : â) in 0..1, g ((b - a) * x + a) = â« (x : â) in 0..1, g ((b - a) * x + a) := rfl,
    rw smul_type_convert (b-a) â« (x : â) in 0..1, g ((b - a) * x + a),
  },
  {
    simp at hneq,
    rw hneq,
    simp,
  }
end 

lemma integral_along_horizontal_line (f:â â E)(a:â)(b:â)(c:â):
  contour_integral f (line_segment (a+c*complex.I) (b+c*complex.I)) = 
  â« (t: â) in a..b, f(t+c*complex.I) :=
begin
  have hr: â« (t: â) in a..b, f(t+c*complex.I) =
    â« (t: â) in a..b, (fâ (complex_affine 1 (c*complex.I))) t:=
    by {rw complex_affine,simp,},
  have hl: (line_segment (âa + âc * complex.I) (âb + âc * complex.I))
    = (complex_affine 1 (c*complex.I)) â (line_segment a b) :=
    by {rw complex_affine, repeat {rw line_segment,}, 
        simp, ext1, simp, ring_nf,},
  rw hr, rw hl,
  rw contour_integral_under_affine _ _ _,
  rw integral_along_reals _ a b,
  simp,
end

lemma integral_along_vertical_line (f:â â E)(a:â)(b:â)(c:â):
  contour_integral f (line_segment (c+a*complex.I) (c+b*complex.I)) = 
  complex.I â¢ â« (t: â) in a..b, f(c+t*complex.I) :=
begin
  have hr: ((Î» t:â, f (âc + ât * complex.I)):â â E)
  = ((Î»t:â, (f â (complex_affine complex.I c)) t):ââ E) := 
    by {rw complex_affine, simp, ext1, ring_nf,},
  have hl:(line_segment (âc + âa * complex.I) (âc + âb * complex.I))
    = (complex_affine complex.I c) â (line_segment a b) :=
    by {repeat {rw complex_affine,}, repeat {rw line_segment,}, 
    simp, ext1, simp, ring_nf,},
  rw hr, rw hl,
  rw contour_integral_under_affine _ _ _,
  rw integral_along_reals _ a b,
end

lemma integral_along_rectangle_bottom(f:â â E)
(l:â)(b:â)(r:â):
  contour_integral f (rec_bottom l b r) 
  = â« (x: â) in l..r, f(x+b*complex.I) :=
  integral_along_horizontal_line f l r b

lemma integral_along_rectangle_right(f:â â E)
(b:â)(r:â)(t:â):
  contour_integral f (rec_right b r t) 
  = complex.I â¢ â« (x: â) in b..t, f(r+x*complex.I) :=
  integral_along_vertical_line f b t r

lemma integral_along_rectangle_top(f:â â E)
(r:â)(t:â)(l:â):
  contour_integral f (rec_top r t l) 
  = - â« (x: â) in l..r, f(x+t*complex.I) :=
  by { unfold rec_top,
       rw integral_along_horizontal_line f r l t,
       rw interval_integral.integral_symm, }

lemma integral_along_rectangle_left(f:â â E)
(t:â)(l:â)(b:â):
  contour_integral f (rec_left t l b) 
  = - complex.I â¢ â« (x: â) in b..t, f(l+x*complex.I) :=
  by { unfold rec_left,
       rw integral_along_vertical_line f t b l,
       rw interval_integral.integral_symm, simp, }

@[protected] lemma integral_along_rectangle_bottomright' 
{f:â â E}{b r t l: â}
(hf: continuous_on f 
  (set.image (rec_bottomright b r t l) (set.interval 0 1))):
  contour_integral f (rec_bottomright b r t l)
  = (contour_integral f (rec_bottom l b r))
  + (contour_integral f (rec_right b r t)):=
contour_integral_along_piecewise_path' hf 
(rec_bottomright_continuous_on b r t l)
(deriv_rec_bottomright_integrable b r t l)

@[protected] lemma integral_along_rectangle_topleft' 
{f:â â E}{b r t l: â}
(hf: continuous_on f 
  (set.image (rec_topleft b r t l) (set.interval 0 1))):
  contour_integral f (rec_topleft b r t l)
  = (contour_integral f (rec_top r t l))
  + (contour_integral f (rec_left t l b)):=
contour_integral_along_piecewise_path' hf 
(rec_topleft_continuous_on b r t l)
(deriv_rec_topleft_integrable b r t l)

theorem integral_along_rectangle'
{f:â â E}{b r t l: â}
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
  rw â add_assoc (contour_integral f (rec_bottom l b r) + 
  contour_integral f (rec_right b r t)) _ _,
  rw add_assoc _ (contour_integral f (rec_right b r t)) 
  (contour_integral f (rec_top r t l) ),
  rw add_comm (contour_integral f (rec_right b r t)) 
  (contour_integral f (rec_top r t l) ),
  rw â add_assoc (contour_integral f (rec_bottom l b r)) _ _,
end

theorem integral_along_rectangle
{f:â â E}{b r t l: â}
(hf: continuous_on f 
  (set.image (rectangle b r t l) (set.interval 0 1))):
  contour_integral f (rectangle b r t l)
  = (((â« (x: â) in l..r, f(x+b*complex.I))
  - (â« (x: â) in l..r, f(x+t*complex.I)))
  + (complex.I â¢ â« (x: â) in b..t, f(r+x*complex.I)))
  - (complex.I â¢ â« (x: â) in b..t, f(l+x*complex.I)) :=
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

theorem Cauchy_Goursat_rectangle_countable {f : â â E} 
{b r t l:â}(bt: bâ¤ t)(lr: lâ¤ r) 
{s: set â}(hs: s.countable)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t)) 
(Hd : â (x : â), x â (set.Ioo l r Ãâ set.Ioo b t) \ s 
â differentiable_at â f x) :
contour_integral f (rectangle b r t l) = 0 :=
begin
  have hf: continuous_on f 
       (set.image (rectangle b r t l) (set.interval 0 1)):=
       continuous_on.mono Hc (image_rectangle_sub_closure bt lr),
  rw integral_along_rectangle hf,
  let z:â:={re:=l,im:=b},
  let w:â:={re:=r,im:=t},
  have z_re : l = z.re := rfl,
  have w_re : r = w.re := rfl,
  have z_im : b = z.im := rfl,
  have w_im : t = w.im := rfl,
  have hl : l = linear_order.min z.re w.re := 
    by {rw [âz_re, âw_re], symmetry, exact min_eq_left lr,},
  have hr : r = linear_order.max z.re w.re := 
    by {rw [âz_re, âw_re], symmetry, exact max_eq_right lr,},
  have hb : b = linear_order.min z.im w.im := 
    by {rw [âz_im, âw_im], symmetry, exact min_eq_left bt,},
  have ht : t = linear_order.max z.im w.im := 
    by {rw [âz_im, âw_im], symmetry, exact max_eq_right bt,},
  rw [z_re, w_re, z_im, w_im] at Hc,
  rw [hl, hr, hb, ht] at Hd,
  have t:=complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable 
           f z w s hs Hc Hd,
  exact t,
end

theorem Cauchy_Goursat_rectangle_singleton {f : â â E} 
(c: â) {b r t l:â}(bt: bâ¤ t)(lr: lâ¤ r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t)) 
(Hd : â (x : â), x â (set.Ioo l r Ãâ set.Ioo b t) \ {c} 
â differentiable_at â f x) :
contour_integral f (rectangle b r t l) = 0 :=
  Cauchy_Goursat_rectangle_countable 
    bt lr (set.to_countable {c}) Hc Hd

theorem Cauchy_Goursat_rectangle{f : â â E} 
{b r t l:â}(bt: bâ¤ t)(lr: lâ¤ r)
(Hc : continuous_on f (set.interval l r Ãâ 
  set.interval b t)) 
(Hd : â (x : â), x â (set.Ioo l r Ãâ set.Ioo b t) 
â differentiable_at â f x) :
contour_integral f (rectangle b r t l) = 0 :=
begin
  apply Cauchy_Goursat_rectangle_singleton 0 bt lr Hc,
  intros x x_in, simp at x_in,
  exact Hd x x_in.1,
end

/-! Part V. Formalize the Cauchy integral formula on rectangles. 

- # Cauchy Integral Formula on Rectangles
-/

lemma dslope_eq_on{f : â â E}{c: â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
set.eq_on (dslope f c) (Î»z:â, (z-c)â»Â¹â¢f(z) - (z-c)â»Â¹â¢f(c)) 
(set.image (rectangle b r t l) (set.interval 0 1)):=
begin
  apply set.eq_on.mono 
    (image_rectangle_sub_compl_center bc ct lc cr),
  have func_eq:(Î»z:â, (z-c)â»Â¹â¢f(z) - (z-c)â»Â¹â¢f(c))=
    slope f c := 
    by {ext1, rw slope_def_module f c x, rw smul_sub,},
  rw func_eq,
  exact eq_on_dslope_slope f c,
end

lemma dslope_continuous_on {f : â â E}{c: â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t))
(Hd : differentiable_on â f (set.Ioo l r Ãâ set.Ioo b t)):
continuous_on (dslope f c) (set.interval l r Ãâ set.interval b t):=
begin
  rw continuous_on_dslope 
    (closure_rectangle_neighborhood' bc ct lc cr),
  split,
  exact Hc,
  exact differentiable_on.differentiable_at Hd 
    (interior_rectangle_neighborhood' bc ct lc cr),
end

lemma dslope_differentiable_at {f : â â E}{c: â}
{b r t l:â}(bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t))
(Hd : differentiable_on â f (set.Ioo l r Ãâ set.Ioo b t)):
â (x : â), x â set.Ioo l r Ãâ set.Ioo b t \ {c} â 
differentiable_at â (dslope f c) x :=
begin
  intros x x_in,
  simp at x_in,
  rw differentiable_at_dslope_of_ne x_in.2,
  have hd:=Hd x x_in.1,
  exact differentiable_within_at.differentiable_at hd
    (interior_rectangle_neighborhood x_in.1),
end

lemma dslope_zero_integral {f : â â E} {c: â}
{b r t l:â} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t))
(Hd : differentiable_on â f (set.Ioo l r Ãâ set.Ioo b t)):
contour_integral (dslope f c) (rectangle b r t l) = 0 :=
begin
  have b_lt_t : b<t := lt_trans bc ct,
  have l_lt_r : l<r := lt_trans lc cr,
  have bt: bâ¤ t:= le_of_lt b_lt_t,
  have lr: lâ¤ r:= le_of_lt l_lt_r,
  apply Cauchy_Goursat_rectangle_singleton c bt lr,
  exact dslope_continuous_on bc ct lc cr Hc Hd,
  exact dslope_differentiable_at bc ct lc cr Hc Hd,
end

lemma part_of_dslope_continuous_on{f : â â E} {c: â}
{b r t l:â} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t)):
continuous_on ((Î» (z : â), (z - c)â»Â¹) â¢ f) 
(rectangle b r t l '' set.interval 0 1) :=
begin 
  have hr: continuous_on (Î» (z : â), (z - c)â»Â¹) 
    (rectangle b r t l '' set.interval 0 1) := 
    continuous_on.mono (reciprocal_continuous_on c)
      (image_rectangle_sub_compl_center bc ct lc cr),
  have ss :(set.interval l r Ãâ set.interval b t) â© {c}á¶
  â (set.interval l r Ãâ set.interval b t) := 
  (set.interval l r Ãâ set.interval b t).inter_subset_left {c}á¶,
  have hf': continuous_on f 
    ((set.interval l r Ãâ set.interval b t) â© {c}á¶) :=
    continuous_on.mono Hc ss,
  have hf: continuous_on f 
    (rectangle b r t l '' set.interval 0 1) :=
    continuous_on.mono hf'
    (image_rectangle_sub_closure_inter_compl_center bc ct lc cr),
  have rf:= continuous_on.prod_map hr hf,
  exact continuous_on.smul hr hf,
end

lemma Cauchy_integral_formula_rectangle_pre{f : â â E} {c: â}
{b r t l:â} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t))
(Hd : differentiable_on â f (set.Ioo l r Ãâ set.Ioo b t)):
contour_integral (Î»z:â, (z-c)â»Â¹â¢f(z)) (rectangle b r t l)=
contour_integral (Î»z:â, (z-c)â»Â¹) (rectangle b r t l) â¢ f(c):=
begin
  rw â contour_integral_smul_right _ _ (f(c)),
  have func_eq:(Î»z:â, (z-c)â»Â¹â¢f(z) - (z-c)â»Â¹â¢f(c))=
  (Î»z:â, (z-c)â»Â¹â¢f(z))-(Î»z:â, (z-c)â»Â¹â¢f(c)):=
    by {ext1, simp,},
  have left_func:(Î» (z : â), (z - c)â»Â¹ â¢ f z) =
  (Î» (z : â), (z - c)â»Â¹) â¢ f:=
    by {ext1, simp,},
  have right_func:(Î» (z : â), (z - c)â»Â¹ â¢ f c) =
  (Î» (z : â), (z - c)â»Â¹) â¢ (Î» (z:â), f c) :=
    by {ext1, simp,},
  have int_z:=dslope_zero_integral bc ct lc cr Hc Hd,
  rw contour_integral_congr (dslope_eq_on bc ct lc cr) at int_z,
  rw func_eq at int_z,
  have int_sub:contour_integral ((Î» (z : â), (z - c)â»Â¹ â¢ f z) - 
  Î» (z : â), (z - c)â»Â¹ â¢ f c) (rectangle b r t l) = 
  contour_integral (Î» (z : â), (z - c)â»Â¹ â¢ f z) (rectangle b r t l) - 
  contour_integral (Î» (z : â), (z - c)â»Â¹ â¢ f c) (rectangle b r t l):=
    begin
      apply contour_integral_sub',
      {
        rw left_func,
        exact part_of_dslope_continuous_on bc ct lc cr Hc,
      },
      {
        rw right_func,
        apply part_of_dslope_continuous_on bc ct lc cr,
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

lemma log_comp_affine_continuous_on{a b:â}{s:set â}
(ha: a â  0)
(h: â (x:â), xâ sâ 0 < (a*x+b).re â¨ (a*x+b).im â  0):
continuous_on (Î» (t : â), (aâ»Â¹*complex.log (a*t + b))) s:=
begin
  apply continuous_on.const_smul _ aâ»Â¹,
  exact is_scalar_tower.has_continuous_const_smul,
  apply continuous_on.clog,
  exact continuous.continuous_on (affine_rtc_continuous a b), 
  exact h,
end

lemma log_comp_affine_has_deriv {a b:â}{x:â}
(ha: a â  0)(h: 0 < (a*x+b).re â¨ (a*x+b).im â  0):
has_deriv_at (Î» (t : â), (aâ»Â¹*complex.log (a*t + b)))
((a*x+b)â»Â¹) x :=
begin 
  have funrw: (Î» (t : â), (aâ»Â¹*complex.log (a*t + b)))
  =(Î» (t : â), (complex.log (a*t + b))*aâ»Â¹):= 
    by {ext1, rw mul_comm,},
  rw funrw,
  have axbrw: (a*x+b)â»Â¹ = (a*(a*x+b)â»Â¹)*aâ»Â¹:=
    by {rw mul_comm _ (a*x+b)â»Â¹, rw mul_assoc,
        have a':a * aâ»Â¹=1:= div_self ha,
        rw a', ring_nf,},
  rw axbrw,
  apply has_deriv_at.mul_const _ aâ»Â¹,
  let f:ââ â:=Î»t:â, (a*t+b),
  have f_rw: (Î» (y : â), complex.log (a * y + b))
  =(Î» (t:â), complex.log (f t)) :=
    by {ext1, simp,},
  have f'f_rw: (a * (a * âx + b)â»Â¹) = a/f x:=
    by {ring_nf,simp,left,rw mul_comm,},
  rw [f_rw, f'f_rw],
  apply has_deriv_at.clog_real,
  simp,
  have coe_comp: f=(Î»t:â, a*t+b) â (Î» (t : â), (t : â)):=
    by {ext1, simp,},
  rw coe_comp,
  have conc:has_deriv_at ((Î» (t : â), a * t + b) â 
    Î» (t : â), ât) a x â 
    has_deriv_at ((Î» (t : â), a * t + b) â 
    Î» (t : â), ât) (a*1) x := by simp,
  rw conc,
  apply has_deriv_at.comp,
  exact complex_affine_has_deriv a b _,
  exact coe_has_deriv _,
  exact h,
end

lemma integral_of_fraction'{a b:â}{lef ref:â}
(ha: a â  0)(hlr: lef â¤ ref)
(h: â (x:â), (xâ (set.Ioo lef ref)) â 
0 < (a*x+b).re â¨ (a*x+b).im â  0)
(hc:continuous_on  (Î» x : â, aâ»Â¹ * complex.log (a * x + b)) 
(set.Icc lef ref))
(hii: interval_integrable (Î» (y : â), (a * ây + b)â»Â¹) 
measure_theory.measure_space.volume lef ref):
â« (t: â) in lef..ref, ((a*t+b)â»Â¹) =
aâ»Â¹*(complex.log (a*ref + b)-complex.log(a*lef+b)):=
begin
  rw mul_sub,
  apply interval_integral.integral_eq_sub_of_has_deriv_at_of_le hlr,
  exact hc,
  intros x x_in,
  have h':= h x x_in,
  exact log_comp_affine_has_deriv ha h',
  exact hii,
end

lemma integral_of_fraction{a b:â}{lef ref:â}
(ha: a â  0)(hlr: lef â¤ ref)
(h: â (x:â), (xâ (set.Icc lef ref)) â 
0 < (a*x+b).re â¨ (a*x+b).im â  0):
â« (t: â) in lef..ref, ((a*t+b)â»Â¹) =
aâ»Â¹*(complex.log (a*ref + b)-complex.log(a*lef+b)):=
begin
  apply integral_of_fraction' ha hlr,
  intros x x_in,
  exact h x (set.Ioo_subset_Icc_self x_in),
  exact log_comp_affine_continuous_on ha h,
  apply continuous_on.interval_integrable,
  apply affine_rtc_continuous_on,
  intros x x_in,
  unfold set.interval at x_in,
  have lef_rw:(min lef ref)=lef:= min_eq_left hlr,
  have ref_rw:(max lef ref)=ref:= max_eq_right hlr,
  rw [lef_rw, ref_rw] at x_in,
  have h'':=h x x_in, intro f,
  rw f at h'', 
  simp at h'', exact h'',
end

lemma integral_of_fraction_one{b:â}{lef ref:â}
(hlr: lef < ref)
(h: â (x:â), (xâ (set.Icc lef ref)) â 
0 < ((x:â)+b).re â¨ ((x:â)+b).im â  0):
â« (t: â) in lef..ref, (((t:â)+b)â»Â¹) =
(complex.log (ref + b)-complex.log(lef+b)) :=
begin
  have one_ne_zero:(1:â)â  0:=by simp,
  have hlr':lefâ¤ ref:= le_of_lt hlr,
  have h':â (x:â), (xâ (set.Icc lef ref)) â 
    0 < ((1:â)*x+b).re â¨ ((1:â)*x+b).im â  0 :=
    by {ring_nf,exact h,},
  have lhs:â« (t: â) in lef..ref, (((t:â)+b)â»Â¹) =
  â« (t: â) in lef..ref, (((1:â)*t+b)â»Â¹):= by simp,
  rw lhs, 
  rw integral_of_fraction one_ne_zero hlr' h',
  simp,
end

lemma integral_of_fraction_I'{b:â}{lef ref:â}
(hlr: lef < ref)
(h: â (x:â), (xâ (set.Ioo lef ref)) â 
0 < (complex.I*x+b:â).re â¨ (complex.I*x+b:â).im â  0)
(hc:continuous_on  (Î» x : â, complex.log (complex.I * x + b)) 
(set.Icc lef ref))
(hii: interval_integrable (Î» (y : â), (complex.I * y + b)â»Â¹) 
measure_theory.measure_space.volume lef ref):
complex.I â¢ â« (t: â) in lef..ref, ((complex.I*t+b:â)â»Â¹) =
(complex.log (complex.I * ref + b)) -
(complex.log (complex.I * lef + b)) :=
begin
  have i_ne_zero:complex.Iâ  0:=complex.I_ne_zero,
  have hlr':lefâ¤ ref:= le_of_lt hlr,
  have hc':continuous_on  (Î» x : â, 
    (complex.I)â»Â¹*complex.log (complex.I * x + b)) 
    (set.Icc lef ref):=
      by { have hcm:=
      continuous_on.const_smul hc (complex.I)â»Â¹,
      simp, simp at hcm, exact hcm,}, 
  rw integral_of_fraction' i_ne_zero hlr' h hc' hii,
  simp, rw â mul_assoc, simp,
end

lemma integral_of_fraction_I{b:â}{lef ref:â}
(hlr: lef < ref)
(h: â (x:â), (xâ (set.Icc lef ref)) â 
0 < (x*complex.I+b:â).re â¨ (x*complex.I+b:â).im â  0):
complex.I â¢ â« (t: â) in lef..ref, ((t*complex.I+b:â)â»Â¹) =
(complex.log (ref*complex.I + b)) -
(complex.log (lef*complex.I + b)) :=
begin
  have i_ne_zero:complex.Iâ  0:=complex.I_ne_zero,
  have hlr':lefâ¤ ref:= le_of_lt hlr,
  have h':â (x:â), (xâ (set.Icc lef ref)) â 
    0 < (complex.I*x+b).re â¨ (complex.I*x+b).im â  0 :=
    by {ring_nf,exact h,},
  have lhs:(Î»t:â,(t*complex.I+b:â)â»Â¹) =
    (Î»t:â ,(complex.I*t+b)â»Â¹):= 
    by {ext1,simp,rw mul_comm},
  rw lhs, 
  rw integral_of_fraction i_ne_zero hlr' h',
  simp, rw â mul_assoc, simp,
  rw mul_comm, rw mul_comm âlef complex.I,
end

lemma integral_of_reciprocal_on_bottom {c: â}
{l b r:â} (bc: b < c.im) (lc: l < c.re) (cr: c.re < r):
contour_integral (Î»z:â, (z-c)â»Â¹) (rec_bottom l b r) = 
complex.log (r+b*complex.I-c) -
complex.log (l+b*complex.I-c) :=
begin
  have lr:l< r:= lt_trans lc cr,
  rw integral_along_rectangle_bottom,
  have lhs: (Î»x:â,(âx + âb * complex.I - c)â»Â¹)=
  (Î»x:â,(âx + (âb * complex.I - c))â»Â¹) := 
    by {ext1, rwâ add_sub,}, rw lhs,
  repeat {rw â add_sub},
  apply integral_of_fraction_one lr, 
  intros x x_in, rw add_sub,
  simp, right, intro f,
  exact (ne_of_lt bc) (zero_symm_exact f),
end

lemma integral_of_reciprocal_on_top {c: â}
{r t l:â} (ct: c.im < t) (lc: l < c.re) (cr: c.re < r):
contour_integral (Î»z:â, (z-c)â»Â¹) (rec_top r t l) = 
complex.log (l+t*complex.I-c) -
complex.log (r+t*complex.I-c) :=
begin
  have lr:l< r:= lt_trans lc cr,
  rw integral_along_rectangle_top,
  rw neg_rewrite, simp,
  have lhs: (Î»x:â,(âx + ât * complex.I - c)â»Â¹)=
  (Î»x:â,(âx + (ât * complex.I - c))â»Â¹) := 
    by {ext1, rwâ add_sub,}, rw lhs,
  repeat {rw â add_sub},
  apply integral_of_fraction_one lr, 
  intros x x_in, rw add_sub,
  simp, right, intro f,
  have f':= zero_symm_exact f,
  rw f' at ct, simp at ct, exact ct,
end

lemma integral_of_reciprocal_on_right {c: â}
{b r t:â} (bc: b < c.im) (ct: c.im < t) (cr: c.re < r) :
contour_integral (Î»z:â, (z-c)â»Â¹) (rec_right b r t) = 
complex.log (r+t*complex.I-c) -
complex.log (r+b*complex.I-c) :=
begin
  have bt : b< t:= lt_trans bc ct,
  rw integral_along_rectangle_right,
  have lhs: (Î»x:â,(âr + âx * complex.I - c)â»Â¹)=
  (Î»x:â,( âx * complex.I +(âr- c))â»Â¹) := 
    by {ext1, ring_nf,}, rw lhs,
  have rtc: âr + ât * complex.I - c =
    ât * complex.I+ (âr-c):= by ring_nf,
  have rbc: âr + âb * complex.I - c =
    âb * complex.I + (âr - c) := by ring_nf,
  rw [rtc, rbc],
  apply integral_of_fraction_I bt,
  intros x x_in, simp,
  left, exact cr,
end

@[protected] lemma integrable_lxc_inv_bt{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
interval_integrable (Î» (x : â), 
(complex.I * âx  + (âl - c))â»Â¹)
measure_theory.measure_space.volume b t :=
begin
  apply continuous_on.interval_integrable,
  apply affine_rtc_continuous_on,
  intros x x_in, intro fp, 
  have rp:(complex.I * âx + (âl - c)).re=l-c.re:=
    by simp,
  rw fp at rp, simp at rp,
  exact (ne_of_lt lc) (zero_exact rp),
end

@[protected] lemma integrable_lxc_inv_bcim{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
interval_integrable (Î» (x : â), 
(complex.I * âx  + (âl - c))â»Â¹) 
measure_theory.measure_space.volume b c.im :=
begin
  have bt: b< t:= (lt_trans bc ct),
  apply interval_integrable.mono_set 
    (integrable_lxc_inv_bt bc ct lc),
  unfold set.interval, 
  rw [min_eq_left_of_lt bc, min_eq_left_of_lt bt,
    max_eq_right_of_lt bc, max_eq_right_of_lt bt],
  exact set.Icc_subset_Icc_right (le_of_lt ct),
end

@[protected] lemma integrable_lxc_inv_cimt{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
interval_integrable (Î» (x : â), 
(complex.I * âx  + (âl - c))â»Â¹) 
measure_theory.measure_space.volume c.im t :=
begin
  have bt: b< t:= (lt_trans bc ct),
  apply interval_integrable.mono_set 
    (integrable_lxc_inv_bt bc ct lc),
  unfold set.interval, 
  rw [min_eq_left_of_lt ct, min_eq_left_of_lt bt,
    max_eq_right_of_lt ct, max_eq_right_of_lt bt],
  exact set.Icc_subset_Icc_left (le_of_lt bc),
end

@[protected] lemma integral_left_two_pieces{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
contour_integral (Î»z:â, (z-c)â»Â¹) (rec_left t l b) 
= -(complex.I â¢ â« (x: â) in (c.im)..t, (l+x*complex.I-c)â»Â¹)
- (complex.I â¢ â« (x: â) in b..(c.im), (l+x*complex.I-c)â»Â¹):=
begin
  rw integral_along_rectangle_left,
  have lhs:-complex.I â¢ â« (x : â) in b..t, 
  (âl + âx * complex.I - c)â»Â¹=-(complex.I â¢ 
  â« (x : â) in b..t, (âl + âx * complex.I - c)â»Â¹):=
    by {simp,}, rw lhs,
  have fr: (Î» (x : â), (âl + âx * complex.I - c)â»Â¹)
  =(Î» (x : â), (complex.I * âx  + (âl - c))â»Â¹) :=
    by {ext1,simp,ring_nf,}, rw fr,
  rw neg_rewrite, simp, symmetry,
  rw â mul_add, simp, left,
  exact interval_integral.integral_add_adjacent_intervals 
    (integrable_lxc_inv_bcim bc ct lc)
    (integrable_lxc_inv_cimt bc ct lc),
end

@[protected] lemma crel{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
c.re - l = complex.abs(l-c.re):=
begin
  have cplx:complex.abs(l-c.re)= 
    complex.abs((l-c.re):â):= by simp,
  rw cplx, 
  have l_sub:(((l-c.re):â):â)=-(((c.re-l):â):â):= by simp,
  rw l_sub, rw complex.abs_neg,
  have c_sub:c.re-lâ¥ 0:=
    by {simp,exact le_of_lt lc,},
  exact (complex.abs_of_nonneg c_sub).symm,
end

@[protected] lemma lcre{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
âl - â(c.re)=complex.I*c.im+(l-c:â) :=
begin
  apply complex.ext,
  simp, simp,
end

@[protected] lemma lcrearg{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
(l - (c.re):â).arg=real.pi :=
begin
  rw complex.arg_eq_pi_iff, split,
  simp, exact lc, simp,
end

lemma integral_on_lower_left{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
â« (x: â) in b..(c.im), (l+x*complex.I-c:â)â»Â¹=
(complex.I)â»Â¹ *(real.log(c.re-l)-real.pi*complex.I-
complex.log (l+b*complex.I-c)) :=
begin
  rw mul_sub,
  have lhs:(Î»x:â,(âl + âx * complex.I - c)â»Â¹)=
  (Î»x:â,( complex.I * âx + (l - c))â»Â¹) := 
    by {ext1, simp, ring_nf,}, rw lhs,
  have rhs: âl + âb * complex.I - c = 
    complex.I * âb + (âl - c) := by ring_nf, rw rhs,
  let F:â â â:=Î» (x : â), 
    ite (x=c.im) (complex.Iâ»Â¹ * 
    (â(real.log (c.re - l)) - âreal.pi * complex.I))
    (complex.Iâ»Â¹*complex.log (complex.I*x + (l-c))),
  have Fx:âx:â, F x=ite (x=c.im) (complex.Iâ»Â¹ * 
    (â(real.log (c.re - l)) - âreal.pi * complex.I))
    (complex.Iâ»Â¹*complex.log (complex.I*x + (l-c))):=
    by {intro x,exact rfl,},
  have Fcim: F c.im = (complex.Iâ»Â¹ * 
    (â(real.log (c.re - l)) - âreal.pi * complex.I)):=
    by {rw Fx c.im, simp,}, rw â Fcim,
  have Fb: F b = complex.Iâ»Â¹ * 
    complex.log (complex.I * âb + (âl - c)) :=
    by {rw Fx b, rw if_neg (ne_of_lt bc),}, rw â Fb,
  have F_eq_on_Ico: set.eq_on 
    (Î»x:â, complex.Iâ»Â¹*complex.log (complex.I*x + (l-c))) 
    F (set.Ico b c.im):=
    by {intros x x_in, simp at x_in,
      have mh:=ne_of_lt x_in.2, rw Fx x,
      rw if_neg mh,},
  have F_eq_on_Ioo:=set.eq_on.mono 
    set.Ioo_subset_Ico_self F_eq_on_Ico,
  apply interval_integral.integral_eq_sub_of_has_deriv_at_of_le 
    (le_of_lt bc),
  {
    intros x x_in,
    by_cases x=c.im,
    {
      rwâ continuous_within_at_diff_self ,
      have iccico:(set.Icc b c.im \ {x})=set.Ico b c.im:=
        by { rw h, exact set.Icc_diff_right,},
      rw iccico,
      unfold continuous_within_at,
      apply tendsto_nhds_within_congr F_eq_on_Ico,
      rw h, rw Fcim, 
      have indu: (Î» (x : â), (Î» (x : â), complex.Iâ»Â¹ * 
      complex.log (complex.I * âx + (âl - c))) x) =
      (Î» (x : â), complex.Iâ»Â¹ * 
      complex.log (complex.I * âx + (âl - c))):= by simp,
      rw indu,
      apply filter.tendsto.const_mul complex.Iâ»Â¹,
      have ftr:(Î» (k : â), complex.log (complex.I * âk + 
      (âl - c)))= complex.log â (Î»k:â, (complex.I * âk + 
      (âl - c))):= by simp, rw ftr,
      apply filter.tendsto.comp,
      rw crel bc ct lc,
      apply complex.tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero,
      simp, exact lc, 
      simp,
      apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
        (Î» (k : â), complex.I * âk + (âl - c)),
      rw lcre bc ct lc,
      apply filter.tendsto.add_const (l-c:â),
      apply filter.tendsto.const_mul complex.I,
      have hs:=coe_differentiable.continuous.continuous_within_at.tendsto,
      simp at hs, simp, exact hs,
      simp, rw eventually_nhds_within_iff,
      rw eventually_nhds_iff,
      use set.univ, split,
      intros new_x x_in_1 x_in_2, 
      simp at x_in_2, exact x_in_2.2,
      split, exact is_open_univ,
      exact set.mem_univ c.im,
    },
    {
      have x_now_in:xâ set.Ico b c.im := 
        by {unfold set.Ico, simp,
          unfold set.Icc at x_in, simp at x_in,
          split, exact x_in.1,
          exact ne.lt_of_le h x_in.2,},
      have Iconhd:set.Ico b c.imâ nhds_within x 
        (set.Icc b c.im):= 
        by {rw mem_nhds_within, use (set.Iio c.im), split,
        exact is_open_Iio, split,
        exact set.Ico_subset_Iio_self x_now_in,
        exact eq.subset Iio_inter_Icc,} ,
      rw â continuous_within_at_inter' Iconhd,
      rw set.inter_comm,
      rw set.inter_eq_left_iff_subset.2 
        set.Ico_subset_Icc_self,
      apply continuous_on.continuous_within_at _ x_now_in,
      apply continuous_on.congr _ 
        (set.eq_on.symm F_eq_on_Ico),
      apply log_comp_affine_continuous_on complex.I_ne_zero,
      intros xx xx_in, simp, right, intro xf,
      simp at xx_in,
      exact (ne_of_lt xx_in.2) (zero_symm_exact xf),
    },
  },
  {
    intros x x_in,
    apply has_eq_deriv_on_Ioo (le_of_lt bc) F_eq_on_Ioo x_in,
    apply log_comp_affine_has_deriv complex.I_ne_zero,
    simp, right, intro ff, simp at x_in,
    exact (ne_of_lt x_in.2) (zero_symm_exact ff),
  },
  {
    exact (integrable_lxc_inv_bcim bc ct lc),
  },
end

lemma integral_on_upper_left{c:â}{t l b:â}
(bc: b < c.im) (ct: c.im < t) (lc: l < c.re):
complex.I â¢ â« (x: â) in (c.im)..t, (l+x*complex.I-c:â)â»Â¹=
(complex.log (l+t*complex.I-c)-
real.log(c.re-l)-real.pi*complex.I) :=
begin
  rw sub_sub,
  have cc: (â(real.log (c.re - l)) 
    + âreal.pi * complex.I) = 
    complex.log ( complex.I * (c.im)+(l - c)) :=
    by {rw â lcre bc ct lc,
        unfold complex.log, rwâ crel bc ct lc,
        simp, left, rwâ lcrearg bc ct lc,},
  rw cc,
  have lhs:(Î»x:â,(âl + âx * complex.I - c)â»Â¹)=
  (Î»x:â,( complex.I * âx + (l - c))â»Â¹) := 
    by {ext1, simp, ring_nf,}, rw lhs,
  have rhs: âl + ât * complex.I - c = 
    complex.I * ât + (âl - c) := by ring_nf, rw rhs,
  apply integral_of_fraction_I' ct,
  {
    intros x x_in,
    simp, simp at x_in,
    right, intro xcim,
    exact (ne_of_lt x_in.1) (zero_symm_exact xcim).symm,
  },
  {
    have func_rw: (Î» (x : â), 
      complex.log (complex.I * âx + (âl - c))) = 
      (Î»(z:â), complex.log z)â 
      (Î»(x:â), (complex.I * âx + (âl - c))) :=
      by {ext1,simp,}, rw func_rw,
    apply continuous_on.comp,
    {
      exact continuous_on_log_of_upper_plane,
    },
    {
      exact (affine_rtc_continuous complex.I (l-c:â)).continuous_on,
    },
    {
      unfold set.maps_to, intros x x_in, 
      simp, simp at x_in, split,
      exact x_in.1,
      intro idd,
      have iddre:(complex.I * âx + (âl - c)).re=0:=
        (congr_arg complex.re idd).trans rfl,
      simp at iddre,
      exact (ne_of_lt lc) (zero_symm_exact iddre),
    },
  },
  {
    exact integrable_lxc_inv_cimt bc ct lc,
  },
end

lemma integral_of_reciprocal_on_left {c: â}
{t l b:â}(bc: b < c.im) (ct: c.im < t) (lc: l < c.re) :
contour_integral (Î»z:â, (z-c)â»Â¹) (rec_left t l b) = 
complex.log (l+b*complex.I-c) -
complex.log (l+t*complex.I-c) + 2*real.pi*complex.I :=
begin
  rw [integral_left_two_pieces bc ct lc,
    integral_on_lower_left bc ct lc,
    integral_on_upper_left bc ct lc],
  simp, rw â mul_assoc, simp, ring_nf,
end

lemma winding_number_of_rectangle {c: â}
{b r t l:â} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r):
contour_integral (Î»z:â, (z-c)â»Â¹) (rectangle b r t l)
= 2 * real.pi *complex.I :=
begin
  rw integral_along_rectangle' 
    (continuous_on.mono
      (reciprocal_continuous_on c)
      (image_rectangle_sub_compl_center bc ct lc cr)),
  rw [integral_of_reciprocal_on_bottom bc lc cr,
    integral_of_reciprocal_on_top ct lc cr,
    integral_of_reciprocal_on_right bc ct cr,
    integral_of_reciprocal_on_left bc ct lc],
  ring_nf,
end

theorem Cauchy_integral_formula_rectangle{f : â â E} {c: â}
{b r t l:â} (bc: b < c.im) (ct: c.im < t)
(lc: l < c.re) (cr: c.re < r)
(Hc : continuous_on f (set.interval l r Ãâ set.interval b t))
(Hd : differentiable_on â f (set.Ioo l r Ãâ set.Ioo b t)):
contour_integral (Î»z:â, (z-c)â»Â¹â¢f(z)) (rectangle b r t l)=
(2 * real.pi *complex.I :â) â¢ f(c) :=
begin
  rw Cauchy_integral_formula_rectangle_pre bc ct lc cr Hc Hd,
  rw winding_number_of_rectangle bc ct lc cr,
end
