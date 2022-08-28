import tactic
import analysis.complex.basic
import analysis.calculus.deriv
import measure_theory.measure.haar_lebesgue
import measure_theory.integral.interval_integral
import data.set.intervals.unordered_interval
import measure_theory.integral.circle_integral
import tomathlib

open num

noncomputable theory

variables {E : Type} 
[normed_add_comm_group E] [normed_space ℂ E] [complete_space E] 

/-! Part O. Convert types 

- # Type Convertion
-/

@[simp] lemma smul_type_convert (a:ℝ)(b:E):
  (a:ℂ)• b = a • b :=
begin
  simp,
end

lemma smul_integral_convert {α:ℂ}{a:ℝ}{b:ℝ}{g:ℝ→ E}:
  α • ∫ (t: ℝ) in a..b, g t = ∫ (t: ℝ) in a..b, α • g t :=
begin
  simp,
end

lemma smul_assoc_convert {α:ℂ}{a:ℂ}{b:E}:
  (α * a) • b = α • a • b :=
begin
  have p1: (α * a) • b = (α • a) • b := by simp,
  have p2: (α • a) • b = α • (a • b) := by apply smul_assoc,
  rw p1,
  rw p2,
end

/-! Part O'. About 2⁻¹  

- # A Half
-/

@[simp] lemma zero_leq_frac_1_2: 0≤ (2⁻¹ : ℝ) := by simp

@[simp] lemma frac_1_2 : (2⁻¹ : ℝ) ≤ 1 := 
  begin
    have h0 : (1 : ℕ) ≤ (2 : ℕ) := by simp,
    have h1 : (1 : ℝ) ≤ (2 : ℝ) :=
    calc
    (1 : ℝ) = (1 : ℕ) : by simp
    ... ≤ (2 : ℕ) : nat.cast_le.elim_right h0
    ... = (2 : ℝ) : by simp,
    have h2 : 0 ≤ (2⁻¹ : ℝ) := by simp,
    have h3 : (1 : ℝ)*(2⁻¹ : ℝ) ≤ (2 : ℝ)*(2⁻¹ : ℝ) := mul_le_mul_of_nonneg_right h1 h2,
    have h4 : (2⁻¹ : ℝ) ≤ 1 :=
    calc
    (2⁻¹ : ℝ) = (1 : ℝ)*(2⁻¹ : ℝ) : by ring_nf
    ... ≤ (2 : ℝ)*(2⁻¹ : ℝ) : h3
    ... = (1 : ℝ) : by ring,
    exact h4,
  end

@[simp] lemma frac_1_2' : (min 2⁻¹ 1 : ℝ) = (2⁻¹ : ℝ) := 
  min_eq_left frac_1_2

@[simp] lemma frac_1_2'': (max 2⁻¹ 1 : ℝ) = (1 : ℝ) :=
  max_eq_right frac_1_2

@[simp] lemma Iiohalf:{a : ℝ | a < 2⁻¹}=set.Iio 2⁻¹ :=
  by rw set.Iio

@[simp] lemma Icchalfone: set.interval (2⁻¹:ℝ) 1 = set.Icc (2⁻¹:ℝ) 1 :=
  by {rw set.interval, rw frac_1_2', rw frac_1_2'',}

lemma frac_1_2_inclusion_left : 
  (set.interval 0 (2⁻¹:ℝ))⊆ (set.interval 0 (1:ℝ)) :=
  by {simp, repeat {rw set.Icc,},simp,
      intros x p q, split, exact p,
      exact le_trans q frac_1_2,}

lemma frac_1_2_inclusion_right :
  (set.interval (2⁻¹:ℝ) 1)⊆ (set.interval 0 (1:ℝ)) :=
  by {simp, repeat {rw set.Icc,}, simp,
      intros a p q, split, 
      exact le_trans zero_leq_frac_1_2 p, exact q,}

/-! Part O''. Aaffine function

- # Affine Function
-/

/- The affine function is a ℝ → ℝ function with the form of t ↦ b + k * t for some k, b ∈ ℝ. -/
def affine_function(k:ℝ)(b:ℝ):ℝ → ℝ := λ t:ℝ , b+k*t

def constant_real_function(k:ℝ):ℝ→ ℝ :=λ t:ℝ , k

lemma affine_function_def(k:ℝ)(b:ℝ): 
affine_function k b=λ t:ℝ , b+k*t := by unfold affine_function

lemma inverse_of_affine{k:ℝ}(hk: k≠ 0)(b:ℝ)(x:ℝ):
(affine_function k b) ((affine_function k⁻¹ (-b/k)) x) = x :=
begin 
  repeat {rw affine_function,},
  simp,
  rw mul_add,
  rw ← mul_assoc,
  have kkinv: k * k⁻¹=1 :=mul_inv_cancel hk,
  rw kkinv,
  have kbk: k*(-b/k)=-b := 
    by {ring_nf,rw mul_comm, rw ← mul_assoc, rw kkinv, ring_nf,},
  rw kbk,
  ring_nf,
end

lemma inverse_of_affine'{k:ℝ}(hk: k≠ 0)(b:ℝ)(x:ℝ):
(affine_function k⁻¹ (-b/k)) ((affine_function k b) x) = x  :=
begin 
  repeat {rw affine_function,},
  simp,
  rw mul_add,
  rw ← mul_assoc,
  have kkinv: k⁻¹ * k =1 :=inv_mul_cancel hk,
  rw kkinv,
  simp, rw ← add_assoc,
  ring_nf,
end

/- The following lemmas prove that the affine function is continuously differentiable. -/
/- In other words, it lies in the C1 space. -/
lemma affine_is_differentiable(k:ℝ)(b:ℝ):
∀ x:ℝ, differentiable_at ℝ (affine_function k b) x :=
begin
  intro,
  unfold affine_function,
  simp,
end

lemma affine_is_differentiable'(k:ℝ)(b:ℝ):
differentiable ℝ (affine_function k b):=
begin
  rw differentiable,
  exact affine_is_differentiable k b,
end

lemma affine_is_continuous(k:ℝ)(b:ℝ):
continuous (affine_function k b):= 
  by {exact differentiable.continuous (affine_is_differentiable' k b),}

lemma affine_is_continuous_on(k:ℝ)(b:ℝ)(lef:ℝ)(ref:ℝ):
continuous_on (affine_function k b) (set.interval lef ref) :=
  (affine_is_continuous k b).continuous_on

lemma deriv_of_affine(k:ℝ)(b:ℝ): 
deriv (affine_function k b) = constant_real_function k :=
begin
  unfold affine_function,
  unfold constant_real_function,
  ext1,
  simp,
end

lemma affine_has_deriv_on_interval(k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ):
∀ x:ℝ , (x ∈ (set.interval lep rep)) → 
(has_deriv_at (affine_function k b) 
((constant_real_function k) x) x) :=
begin
  intro,
  intro q,
  rw ← deriv_of_affine k b,
  apply differentiable_at.has_deriv_at 
    ((affine_is_differentiable k b) x),
end

lemma affine_in_C1_on_interval(k:ℝ)(lep:ℝ)(rep:ℝ):
continuous_on (constant_real_function k) 
(set.interval lep rep) := 
begin
  unfold constant_real_function,
  exact continuous_on_const,
end

/- The derivative of a path composed by an affine function -/
lemma deriv_of_path_affine_comp_pre
(k:ℝ)(b:ℝ)(L:ℝ → ℂ):
deriv (L ∘ (affine_function k b)) 
= (deriv (affine_function k b)) 
• (deriv L ∘ (affine_function k b)):=
begin
  have hk: k = 0 ∨ k ≠ 0 := em (k = 0),
  cases hk, rw hk, ext1,
  rw affine_function, simp,
  ext1,
  have q:differentiable_at ℝ (affine_function k b) x 
    :=affine_is_differentiable k b x,
  have dcond:
  differentiable_at ℝ L ((affine_function k b) x) 
  ∨ ¬ differentiable_at ℝ L ((affine_function k b) x) :=
    em (differentiable_at ℝ L ((affine_function k b) x) ),
  cases dcond,
  exact deriv.scomp x dcond q,
  simp,
  have dlhx: deriv L ((affine_function k b) x) = 0 :=
    deriv_zero_of_not_differentiable_at dcond,
  rw dlhx,
  simp,
  apply deriv_zero_of_not_differentiable_at,
  intro drlhx,
  have Lhh: L= (L∘ (affine_function k b)) ∘ 
    (affine_function k⁻¹ (-b/k)) :=
    by {ext1,simp,rw inverse_of_affine hk b _,},
  rw Lhh at dcond,
  apply dcond, apply differentiable_at.comp,
  rw inverse_of_affine' hk b _,
  exact drlhx,
  exact affine_is_differentiable' _ _ _,
end  

lemma deriv_of_path_affine_comp
(k:ℝ)(b:ℝ)(L:ℝ → ℂ):
deriv (L ∘ (affine_function k b)) 
= k • (deriv L ∘ (affine_function k b)):=
begin
  have p:=deriv_of_path_affine_comp_pre k b L,
  rw deriv_of_affine k b at p,
  exact p,
end

/-! Part I. Path: definition and basic properties

- # Path
A path is any function L defined as ℝ → ℂ
-/

def constant_path (z:ℂ):ℝ → ℂ :=λ (t:ℝ ), z 

/-- The path concatenation of two path means compressing their domain [0,1] to [0, 1/2] (and [1/2, 1]) then concate them back to [0,1].-/
def path_concatenation {L1:ℝ → ℂ}{L2:ℝ →ℂ}
(hw: L1 1=L2 0):ℝ → ℂ :=
λ (t:ℝ), if t<2⁻¹ then L1 (2*t) else L2 (-1+2*t)

/-- The inverse of a path is to reverse the direction of a path. -/
def path_inverse(L:ℝ → ℂ):ℝ → ℂ := λ (t:ℝ ), L(1-t) 

lemma path_concatenation_endpoint {L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0): path_concatenation hw 1=L2 1:=
begin
  rw path_concatenation,
  have m:¬ (1<(2⁻¹ : ℝ)):=by simp,
  ring_nf,
  simp,
  intro f,
  exfalso,
  finish,
end

lemma path_concatenation_left{L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0){t:ℝ}(ht: t<=2⁻¹):
path_concatenation hw t = L1 (2*t):=
begin
  rw path_concatenation,
  by_cases t<2⁻¹,
  simp,
  intro p,
  exfalso,
  have hn:¬ t<2⁻¹:=by {simp,exact p},
  exact hn h,
  simp at *,
  have hh: t=2⁻¹:=by {exact ge_antisymm h ht},
  rw hh,
  simp,
  rwa hw,
end 

lemma path_concatenation_right{L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0){t:ℝ}(ht: t>=2⁻¹):
path_concatenation hw t = L2 (-1+2*t):=
begin
  rw path_concatenation,
  simp,
  intro p,
  exfalso,
  have pn:¬ t<2⁻¹:=by {simp at *,exact ht},
  exact pn p,
end

lemma path_concatenation_left'{L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0):set.eq_on ((λ t:ℝ, L1 (2*t)):ℝ → ℂ) 
((λ t:ℝ, path_concatenation hw t):ℝ → ℂ)
(set.interval (0:ℝ) 2⁻¹):=
begin
  rw set.eq_on,
  intro x,
  intro in_condition,
  simp at in_condition, symmetry,
  exact path_concatenation_left hw in_condition.2,
end

lemma path_concatenation_right'{L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0):set.eq_on ((λ t:ℝ, L2 (-1+2*t)):ℝ → ℂ) 
((λ t:ℝ, path_concatenation hw t):ℝ → ℂ)
(set.interval 2⁻¹ (1:ℝ)):=
begin
  rw set.eq_on,
  intro x,
  intro in_condition, symmetry,
  apply path_concatenation_right,
  rw[ge],
  rw set.interval at in_condition,
  have h0 : (min 2⁻¹ 1 : ℝ) ≤ x := and.elim_left ((iff.elim_left set.mem_Icc) in_condition),
  have h4 : 2⁻¹ ≤ x := 
    calc 2⁻¹ = (min 2⁻¹ 1 : ℝ) : by simp
    ... ≤ x : h0,
  exact h4,
end

lemma path_concatenation_image{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0):
set.image (path_concatenation hw) (set.interval 0 1)
=(set.image L1 (set.interval 0 1))∪ 
(set.image L2 (set.interval 0 1)) :=
begin
  ext1, split,
  have md: (0:ℝ)<(2:ℝ):= by simp,
  have mn: (0:ℝ)≤(2:ℝ):= le_of_lt md,
  intro x_in,
  rw path_concatenation at *,
  simp, simp at x_in,
  cases x_in with x',
  by_cases x'<(2⁻¹:ℝ),
  rw if_pos h at x_in_h, 
  left, use 2*x',
  split, split,
  simp, exact x_in_h.1.1,
  apply le_of_lt,
  have t:=mul_lt_mul_of_pos_left h md, 
  simp at t, exact t, exact x_in_h.2,
  rw if_neg h at x_in_h, 
  right, use (-1+2*x'),
  simp at h, split, split, 
  simp, have t:=mul_le_mul_of_nonneg_left h mn,
  simp at t, exact t, 
  simp, ring_nf, simp, exact x_in_h.1.2,
  exact x_in_h.2,
  intro x_in,
  rw path_concatenation at *, 
  simp, simp at x_in,
  cases x_in, cases x_in with x',
  use (2⁻¹:ℝ)*x',
  simp, split, split,
  exact x_in_h.1.1,
  have t:=mul_le_mul_of_nonneg_left x_in_h.1.2 zero_leq_frac_1_2,
  apply le_trans t, simp,
  by_cases x'<1,
  rw if_pos h, exact x_in_h.2,
  rw if_neg h, simp at h,
  have t:x'=1 :=
    by {apply ge_antisymm, exact h, exact x_in_h.1.2,},
  rw t, rw t at x_in_h, simp,
  rw ← hw, exact x_in_h.2,
  cases x_in with x',
  use (2⁻¹:ℝ)*(1+x'),
  simp, split, split,
  apply le_trans x_in_h.1.1,
  simp, 
  have t:=add_le_add_left x_in_h.1.2 1, 
  have tt:=mul_le_mul_of_nonneg_left t zero_leq_frac_1_2,
  apply le_trans tt, ring_nf,
  have xneg:¬ x'<0:= by {simp, exact x_in_h.1.1,},
  rw if_neg xneg, exact x_in_h.2,
end

lemma path_concatenation_image_left_subset
{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0):
set.image L1 (set.interval 0 1) ⊆ 
set.image (path_concatenation hw) (set.interval 0 1):=
by { rw path_concatenation_image hw,
     exact (L1 '' set.interval 0 1).subset_union_left 
       (L2 '' set.interval 0 1), }

lemma path_concatenation_image_right_subset
{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0):
set.image L2 (set.interval 0 1) ⊆ 
set.image (path_concatenation hw) (set.interval 0 1):=
by { rw path_concatenation_image hw,
     exact (L1 '' set.interval 0 1).subset_union_right 
       (L2 '' set.interval 0 1), }

lemma continuity_of_constant_path (z:ℂ): continuous (constant_path z):=
begin
  rw constant_path,
  exact continuous_const,
end

lemma general_piece_continuous_on(L:ℝ→ ℂ)
{k:ℝ}(hk:0 ≤ k)(b:ℝ)(lef:ℝ)(ref:ℝ)
(hlc:continuous_on L (set.interval (b+k*lef) (b+k*ref))):
continuous_on (λt:ℝ, L(b+k*t)) (set.interval lef ref) :=
begin
  have p:(λt:ℝ, L(b+k*t))=L∘(affine_function k b) :=
    by {ext1, rw affine_function, },
  rw p,
  apply continuous_on.comp,
  exact hlc,
  exact affine_is_continuous_on k b _ _,
  rw set.maps_to,
  intros x hx,
  rw set.interval at *, rw affine_function,
  simp at *, split,
  cases hx.1 with hx1, 
  left, exact mul_le_mul_of_nonneg_left hx1 hk,
  right, exact mul_le_mul_of_nonneg_left h hk,
  cases hx.2 with hx2,
  left, exact mul_le_mul_of_nonneg_left hx2 hk,
  right, exact mul_le_mul_of_nonneg_left h hk,
end

lemma path_concatenation_continuous_on{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0)
(hl1c:continuous_on L1 (set.interval 0 1))
(hl2c:continuous_on L2 (set.interval 0 1)):
continuous_on (path_concatenation hw) (set.interval 0 1):=
begin
  have twogeqzero:(2:ℝ)≥ (0:ℝ):=by simp,
  apply continuous_on.if,
  {
    intros a ha,
    rw Iiohalf at ha,
    rw frontier_Iio at ha,
    simp at ha,
    rw ha.2, simp, exact hw,
  },
  {
    rw Iiohalf, rw closure_Iio,
    simp,
    have fr:=frac_1_2, 
    have mp: (set.Icc (0:ℝ) 1 ∩ set.Iic (2⁻¹:ℝ))=set.interval 0 (2⁻¹:ℝ):=
      begin
        repeat {rw set.Icc,}, rw set.Iic, ext1,
        simp, intros p q, exact le_trans p fr,
      end,
    rw mp,
    have gc:=general_piece_continuous_on L1 twogeqzero 0 0 2⁻¹,
    ring_nf at gc, ring_nf,
    apply gc, exact hl1c,
  },
  {
    have Icihalf:{a : ℝ | ¬a < 2⁻¹}=set.Ici 2⁻¹:=
      by {rw set.Ici,ext1,simp,},
    rw Icihalf, rw closure_Ici, simp,
    have mp: (set.Icc 0 1 ∩ set.Ici 2⁻¹)=set.interval (2⁻¹:ℝ) 1:=
      begin
        rw Icchalfone, repeat {rw set.Icc,}, rw set.Ici, 
        ext1, simp, split, intro fc, split, exact fc.2,
        exact fc.1.2, intro fc, split, split,
        exact le_trans zero_leq_frac_1_2 fc.1,
        exact fc.2, exact fc.1
      end, 
    rw mp,
    have gc:=general_piece_continuous_on L2 twogeqzero (-1) 2⁻¹ 1,
    ring_nf at gc, ring_nf,
    apply gc, exact hl2c,
  },
end

lemma path_concatenation_continuous{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0)
(hl1c:continuous L1)(hl2c:continuous L2):
continuous (path_concatenation hw):=
begin
  apply continuous.if,
  {
    intros a af,
    rw Iiohalf at af, rw frontier_Iio at af,
    simp at af, rw af, simp, exact hw,
  },
  {
    have p:(λt:ℝ, L1(2*t))=L1∘(affine_function 2 0) :=
      by {ext1, rw affine_function, simp,},
    rw p,
    exact continuous.comp hl1c (affine_is_continuous _ _),
  },
  {
    have p:(λt:ℝ, L2(-1+2*t))=L2∘(affine_function 2 (-1)) :=
      by {ext1, rw affine_function, },
    rw p,
    exact continuous.comp hl2c (affine_is_continuous _ _),
  },
end

lemma has_eq_deriv_on_Ioo{f:ℝ→ ℂ}{g:ℝ→ ℂ}{a b x:ℝ}{d:ℂ}
(hab:a≤ b)(hde: set.eq_on f g (set.Ioo a b))
(hx: x ∈ set.Ioo a b)(hfx: has_deriv_at f d x):
has_deriv_at g d x:=
begin
  apply has_deriv_at.congr_of_eventually_eq hfx,
  symmetry,
  unfold filter.eventually_eq,
  apply iff.elim_right eventually_nhds_eq_iff,
  existsi (set.Ioo a b),
  apply and.intro,
  exact hde,
  split,
  exact is_open_Ioo,
  exact hx,
end

lemma deriv_eq_on_Ioo{f:ℝ→ ℂ}{g:ℝ→ ℂ}{a b:ℝ}(hab:a≤ b)
(hde: set.eq_on f g (set.Ioo a b)):
set.eq_on (deriv f) (deriv g) (set.Ioo a b):=
begin
  rw set.eq_on,
  intros x hx,
  apply filter.eventually_eq.deriv_eq,
  unfold filter.eventually_eq,
  apply iff.elim_right eventually_nhds_eq_iff,
  existsi (set.Ioo a b),
  apply and.intro,
  exact hde,
  split,
  exact is_open_Ioo,
  exact hx,
end

lemma deriv_eq_on{f:ℝ→ ℂ}{g:ℝ→ ℂ}{a b:ℝ}(hab:a≤ b)
(hde: set.eq_on f g (set.interval a b)):
set.eq_on (deriv f) (deriv g) (set.Ioo a b):=
deriv_eq_on_Ioo hab 
(set.eq_on.mono Ioo_subset_interval hde)

@[protected] lemma deriv_L1_eq_on{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0):
set.eq_on (deriv (λ t:ℝ, L1 (2*t))) 
(deriv (path_concatenation hw)) (set.Ioo (0:ℝ) 2⁻¹):=
begin
  apply deriv_eq_on,
  simp,
  exact path_concatenation_left' hw,
end

@[protected] lemma deriv_L2_eq_on{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0):
set.eq_on (deriv (λ t:ℝ, L2 (-1+2*t))) 
(deriv (path_concatenation hw)) (set.Ioo 2⁻¹ (1:ℝ)):=
begin
  apply deriv_eq_on,
  simp,
  exact path_concatenation_right' hw,
end

lemma interval_integrable_iff_integrable_Ioo_volume
(f : ℝ → E) {a b : ℝ} (hab : a ≤ b):
  interval_integrable f measure_theory.measure_space.volume a b ↔ 
  measure_theory.integrable_on f (set.Ioo a b) measure_theory.measure_space.volume :=
begin
  apply interval_integrable_iff_integrable_Ioo_of_le hab,
  exact _inst_2,
  exact _inst_3,
  exact real.has_no_atoms_volume,
end

lemma path_comp_affine_deriv_integrable(L:ℝ→ ℂ)
{k:ℝ}(hk:k≠ 0)(b:ℝ)
(hli:interval_integrable (deriv L) measure_theory.measure_space.volume 0 1):
interval_integrable (deriv (λ t:ℝ, L (b+k*t)))
  measure_theory.measure_space.volume (-b/k) ((1-b)/k) :=
begin
  have m:(λ t:ℝ, L (b+k*t))=L∘ (affine_function k b):=
    by {ext1,rw affine_function,},
  rw m,
  rw deriv_of_path_affine_comp k b L,
  apply interval_integrable.smul,
  let f:=λ(t:ℝ), deriv L (b+t),
  let g:=λ(t:ℝ), deriv L t,
  have rf: (deriv L ∘ affine_function k b) = (λ(t:ℝ), f(k*t)):=
    by {ext1, rw affine_function, },
  have rg: f = (λ(t:ℝ), g(b+t)) := 
    by {ext1, simp,},
  rw rf,
  apply interval_integrable.comp_mul_left,
  rw rg,
  have minusb: -b=0-b:= by ring_nf, rw minusb,
  apply integrable_comp_add_left,
  exact hli,
end

lemma path_concatenation_deriv_integrable{L1:ℝ→ ℂ}{L2:ℝ → ℂ}
(hw: L1 1=L2 0)
(hl1i:interval_integrable (deriv L1) measure_theory.measure_space.volume 0 1)
(hl2i:interval_integrable (deriv L2) measure_theory.measure_space.volume 0 1):
interval_integrable (deriv (path_concatenation hw))
measure_theory.measure_space.volume 0 1 :=
begin
  have ze_leq_one:(0:ℝ)≤ (1:ℝ):= by simp,
  have two_ne_zero: (2:ℝ)≠ (0:ℝ):= by simp,
  have hl1i':=path_comp_affine_deriv_integrable L1 two_ne_zero 0 hl1i,
  have hl2i':=path_comp_affine_deriv_integrable L2 two_ne_zero (-1) hl2i,
  simp at hl1i', simp at hl2i',
  apply interval_integrable.trans,
  {
    rw interval_integrable_iff_integrable_Ioo_volume 
      (deriv (path_concatenation hw)) zero_leq_frac_1_2,
    apply measure_theory.integrable_on.congr_fun,
    {
      rw ← interval_integrable_iff_integrable_Ioo_volume _ zero_leq_frac_1_2,
      exact hl1i',
      exact normed_field.to_normed_space,
      exact complete_of_proper,
    },
    {
      exact deriv_L1_eq_on hw,
    },
    {
      exact measurable_set_Ioo,
    },
  },
  {
    rw interval_integrable_iff_integrable_Ioo_volume 
      (deriv (path_concatenation hw)) frac_1_2,
    apply measure_theory.integrable_on.congr_fun,
    {
      rw ← interval_integrable_iff_integrable_Ioo_volume _ frac_1_2,
      exact hl2i',
      exact normed_field.to_normed_space,
      exact complete_of_proper,
    },
    {
      exact deriv_L2_eq_on hw,
    },
    {
      exact measurable_set_Ioo,
    },
  },
end

/-! Part II. Integrability along a contour

- # Contour Integrability
-/

def contour_integrable (f : ℂ → E) (L: ℝ → ℂ): Prop :=
interval_integrable (λ (x : ℝ), deriv L x • f (L x)) 
  measure_theory.measure_space.volume 0 1

lemma contour_integrable_smul_continuous_on{f:ℂ → E}{L:ℝ → ℂ}
(hf: continuous_on f (set.image L (set.interval 0 1)))
(hl: continuous_on L (set.interval 0 1))
(hli: interval_integrable (deriv L) measure_theory.measure_space.volume 0 1):
  contour_integrable f L :=
begin
  apply interval_integrable.smul_continuous_on,
  {
    exact hli,
  },
  {
    simp at *,
    apply continuous_on.comp,
    {
      exact hf,
    },
    {
      exact hl,
    },
    {
      simp,
      rw set.maps_to,
      intros x x_in,
      simp,
      use x, split,
      simp at x_in, exact x_in,
      exact rfl,
    },
  },
end

lemma contour_integrable_zero (L:ℝ → ℂ):
contour_integrable (λt:ℂ, (0:E)) L := 
  by {unfold contour_integrable, simp, }

lemma contour_integrable_neg {f:ℂ → E}{L:ℝ → ℂ}
(h: contour_integrable f L):
contour_integrable (-f) L :=
  by {unfold contour_integrable at *, simp,
  exact interval_integrable.neg h,}

lemma contour_integrable_smul {f:ℂ → E}{L:ℝ → ℂ}
(h: contour_integrable f L)(α:ℂ):
contour_integrable (α • f) L :=
begin
  unfold contour_integrable at *, 
  have mid:(λt:ℝ, deriv L t • (α • f) (L t))
      =(λt:ℝ, α • deriv L t • f (L t)):=
    by {ext1, simp, rw smul_comm,},
  rw mid, 
  exact interval_integrable.smul h _,
end

/-! Part III. Contour Integral: definition and basic properties 

- # Contour Integral
-/

def contour_integral (f : ℂ → E) (L: ℝ → ℂ): E :=
∫ (t: ℝ ) in 0..1, (deriv L t) • f(L t) 

@[simp] lemma contour_integral_zero (L:ℝ → ℂ):
contour_integral (λt:ℂ, (0:E)) L = 0 :=
  by {unfold contour_integral, simp, }

lemma contour_integral_neg (f:ℂ → E)(L:ℝ → ℂ):
contour_integral (-f) L = - contour_integral f L :=
  by {unfold contour_integral, simp,}

lemma contour_integral_smul (f:ℂ → E)(L:ℝ → ℂ)(α:ℂ):
contour_integral (α • f) L = α • contour_integral f L :=
begin
  unfold contour_integral,
  have mid:(λt:ℝ, deriv L t • (α • f) (L t))
      =(λt:ℝ, α • deriv L t • f (L t)):=
    by {ext1, simp, rw smul_comm,},
  rw mid,
  rw smul_integral_convert,
end

lemma contour_integral_smul_right(f:ℂ → ℂ)(L:ℝ → ℂ)(c:E):
contour_integral (λz:ℂ, f(z) • c) L = 
(contour_integral f L) • c :=
begin
  unfold contour_integral,
  have func_rw: (λ t:ℝ,deriv L t • f (L t) • c) =
  (λ t:ℝ,(deriv L t • f (L t)) • c) :=
    by {ext1, rw smul_assoc,},
  rw func_rw,
  simp,
end

lemma contour_integral_add{f:ℂ → E}{g:ℂ → E}{L:ℝ → ℂ}
(hfL: contour_integrable f L)(hgL: contour_integrable g L):
contour_integral (f + g) L = 
contour_integral f L + contour_integral g L :=
begin
  unfold contour_integral, simp,
  apply interval_integral.integral_add,
  exact hfL, exact hgL,
end

lemma contour_integral_add' {f:ℂ → E}{g:ℂ → E}{L:ℝ → ℂ}
(hf: continuous_on f (set.image L (set.interval 0 1)))
(hg: continuous_on g (set.image L (set.interval 0 1)))
(hl: continuous_on L (set.interval 0 1))
(hli: interval_integrable (deriv L) measure_theory.measure_space.volume 0 1):
contour_integral (f + g) L = 
contour_integral f L + contour_integral g L :=
begin
  apply contour_integral_add,
  exact contour_integrable_smul_continuous_on hf hl hli,
  exact contour_integrable_smul_continuous_on hg hl hli,
end 

lemma contour_integral_sub{f:ℂ → E}{g:ℂ → E}{L:ℝ → ℂ}
(hfL: contour_integrable f L)(hgL: contour_integrable g L):
contour_integral (f - g) L = 
contour_integral f L - contour_integral g L :=
begin
  unfold contour_integral, simp, 
  have p:(λt:ℝ,deriv L t • (f (L t) - g (L t)))=
  (λt:ℝ, deriv L t • f (L t) - deriv L t • g (L t)) :=
    by {ext1, exact smul_sub _ (f(L x)) (g(L x)),},
  rw p,
  apply interval_integral.integral_sub,
  exact hfL, exact hgL,
end

lemma contour_integral_sub' {f:ℂ → E}{g:ℂ → E}{L:ℝ → ℂ}
(hf: continuous_on f (set.image L (set.interval 0 1)))
(hg: continuous_on g (set.image L (set.interval 0 1)))
(hl: continuous_on L (set.interval 0 1))
(hli: interval_integrable (deriv L) measure_theory.measure_space.volume 0 1):
contour_integral (f - g) L = 
contour_integral f L - contour_integral g L :=
begin
  apply contour_integral_sub,
  exact contour_integrable_smul_continuous_on hf hl hli,
  exact contour_integrable_smul_continuous_on hg hl hli,
end 

/-! Part IV. Integral is an addictive function of the path

- # Addictivity
-/

lemma contour_integral_congr {f g: ℂ → E}{L:ℝ→ ℂ}
(hfg: set.eq_on f g (set.image L (set.interval 0 1))):
contour_integral f L = contour_integral g L :=
begin
  unfold contour_integral,
  apply interval_integral.integral_congr,
  intros x x_in, simp,
  have Lx_in: L x∈ (set.image L (set.interval 0 1)):=
    set.mem_image_of_mem L x_in,
  have hfg':=hfg Lx_in,
  rwa hfg',
end

@[simp] lemma contour_integral_along_constant_path 
(f : ℂ → E) (z:ℂ) :
contour_integral f (constant_path z) = 0 :=
begin
  unfold contour_integral,
  have p:deriv  (constant_path z) =0 :=
    begin
      ext1,
      unfold constant_path,
      simp,
    end,
  rw p,
  simp,
end

@[protected] lemma genearl_term_of_sum' (f : ℂ → E)(L:ℝ → ℂ)
(k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ):
∫ (t : ℝ) in b+k*lep..b+k*rep, deriv L t • f (L t) 
= ∫ (t : ℝ) in lep..rep, 
deriv (L ∘ (affine_function k b)) t • f (L (b+k*t)):=
begin
  rw deriv_of_path_affine_comp,
  rw ← interval_integral.smul_integral_comp_add_mul _ k b,
  rw affine_function,
  simp,
  simp [smul_assoc_convert],
end

@[protected] lemma genearl_term_of_sum (f : ℂ → E)(L:ℝ → ℂ)
(k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ):
∫ (t : ℝ) in b+k*lep..b+k*rep, deriv L t • f (L t) 
= ∫ (t : ℝ) in lep..rep, 
deriv (λ(t:ℝ), L(b+k*t)) t • f (L (b+k*t)) :=
begin
  have p:deriv (λ(t:ℝ), L(b+k*t))
    = deriv (L ∘ (affine_function k b)) :=
    by {ext1,rw affine_function,},
  rw p,
  exact genearl_term_of_sum' _ _ _ _ _ _,
end

@[protected] lemma first_term_of_sum(f : ℂ → E)(L1:ℝ → ℂ): 
∫ (t : ℝ) in 0..1, deriv L1 t • f (L1 t) 
= ∫ (t : ℝ) in 0..2⁻¹, 
deriv (λ(t:ℝ),L1 (2*t)) t • f (L1 (2*t)) :=
begin
  have p:(λ t:ℝ,deriv (λ(x:ℝ),L1 (2*x)) t • f (L1 (2*t)))
  =(λ t:ℝ,deriv (λ(x:ℝ),L1 (0+2*x)) t • f (L1 (0+2*t))) := 
    by simp,
  rw p,
  rw ← genearl_term_of_sum f L1 2 0 0 2⁻¹,
  simp,
end

@[protected] lemma second_term_of_sum(f : ℂ → E)(L2:ℝ → ℂ): 
∫ (t : ℝ) in 0..1, deriv L2 t • f (L2 t) 
= ∫ (t : ℝ) in 2⁻¹..1, 
deriv (λ(t:ℝ),L2 (-1+2*t)) t • f (L2 (-1+2*t)) :=
begin
  rw ← genearl_term_of_sum f L2 2 (-1) 2⁻¹ 1,
  simp,
  have q: (-1)+2 = (1:ℝ) :=by ring,
  rw q,
end

@[protected] lemma first_func_in_term(f : ℂ → E)
{L1:ℝ → ℂ}{L2:ℝ → ℂ} (hw: L1 1=L2 0):
set.eq_on (λ t:ℝ, deriv (λ(x:ℝ),L1 (2*x)) t • f (L1 (2*t))) 
(λ t:ℝ, deriv (path_concatenation hw) t • f (path_concatenation hw t)) 
(set.Ioo (0:ℝ) 2⁻¹) :=
begin
  rw set.eq_on,
  intros x x_in,
  rw deriv_L1_eq_on hw x_in,
  have ip: (set.Ioo (0:ℝ) 2⁻¹)⊆ (set.interval (0:ℝ) 2⁻¹) := 
    by {simp,exact set.Ioo_subset_Icc_self},
  have x_in':x∈ (set.interval (0:ℝ) 2⁻¹) := ip x_in,
  have t:=path_concatenation_left' hw x_in', simp at t, rw t,
end

@[protected] lemma second_func_in_term(f : ℂ → E)
{L1:ℝ → ℂ}{L2:ℝ → ℂ} (hw: L1 1=L2 0):
set.eq_on (λt:ℝ,deriv (λ(x:ℝ),L2 (-1+2*x)) t • f (L2 (-1+2*t)))
(λ t:ℝ, deriv (path_concatenation hw) t • f (path_concatenation hw t)) 
(set.Ioo (2⁻¹:ℝ) 1) :=
begin
  rw set.eq_on,
  intros x x_in,
  rw deriv_L2_eq_on hw x_in,
  have ip: (set.Ioo (2⁻¹:ℝ) 1)⊆ (set.interval (2⁻¹:ℝ) 1) := 
    by {simp,exact set.Ioo_subset_Icc_self},
  have x_in':x∈ (set.interval (2⁻¹:ℝ) 1) := ip x_in,
  have t:=path_concatenation_right' hw x_in', simp at t, rw t,
end

@[protected] lemma contour_integral_first_piece (f : ℂ → E)
{L1:ℝ → ℂ}{L2:ℝ → ℂ} (hw: L1 1=L2 0):
contour_integral f L1 = 
(∫ (t : ℝ) in 0..2⁻¹, deriv (path_concatenation hw) t • f (path_concatenation hw t) ) :=
begin
  unfold contour_integral, rw first_term_of_sum,
  rw integral_congr''' zero_leq_frac_1_2 (first_func_in_term f hw),
  exact real.has_no_atoms_volume,
end

@[protected] lemma contour_integral_second_piece (f : ℂ → E)
{L1:ℝ → ℂ}{L2:ℝ → ℂ} (hw: L1 1=L2 0):
contour_integral f L2 = 
(∫ (t : ℝ) in 2⁻¹..1, deriv (path_concatenation hw) t • f (path_concatenation hw t) ) :=
begin
  unfold contour_integral, rw second_term_of_sum,
  rw integral_congr''' frac_1_2 (second_func_in_term f hw),
  exact real.has_no_atoms_volume,
end

/- The integral along the path L1∪L2 is equal to the sum of integrals along L1 and L2. -/
theorem contour_integral_along_piecewise_path{f : ℂ → E}
{L1:ℝ → ℂ}{L2:ℝ → ℂ} {hw: L1 1=L2 0}
(hi: contour_integrable f (path_concatenation hw)):
contour_integral f (path_concatenation hw) = 
contour_integral f L1 + contour_integral f L2 :=
begin
  unfold contour_integrable at hi,
  rw [contour_integral_first_piece f hw, 
      contour_integral_second_piece f hw,
      contour_integral], symmetry,
  apply interval_integral.integral_add_adjacent_intervals,
  exact interval_integrable.mono_set hi frac_1_2_inclusion_left,
  exact interval_integrable.mono_set hi frac_1_2_inclusion_right,
end

/- A useful version of the previous theorem -/
theorem contour_integral_along_piecewise_path'{f : ℂ → E}
{L1:ℝ → ℂ}{L2:ℝ → ℂ} {hw: L1 1=L2 0}
(hf: continuous_on f (set.image (path_concatenation hw) (set.interval 0 1)))
(hlc: continuous_on (path_concatenation hw) (set.interval 0 1))
(hli: interval_integrable (deriv ((path_concatenation hw))) 
       measure_theory.measure_space.volume 0 1):
contour_integral f (path_concatenation hw) = 
contour_integral f L1 + contour_integral f L2 :=
contour_integral_along_piecewise_path
(contour_integrable_smul_continuous_on hf hlc hli)

/- Even more useful -/
theorem contour_integral_along_piecewise_path''{f : ℂ → E}
{L1:ℝ → ℂ}{L2:ℝ → ℂ} {hw: L1 1=L2 0}
(hf: continuous_on f ((set.image L1 (set.interval 0 1))∪ 
     (set.image L2 (set.interval 0 1))))
(hl1c: continuous_on L1 (set.interval 0 1))
(hl2c: continuous_on L2 (set.interval 0 1))
(hl1i: interval_integrable (deriv L1) measure_theory.measure_space.volume 0 1)
(hl2i: interval_integrable (deriv L2) measure_theory.measure_space.volume 0 1):
contour_integral f (path_concatenation hw) = 
contour_integral f L1 + contour_integral f L2 :=
begin
  apply contour_integral_along_piecewise_path',
  rw ← path_concatenation_image hw at hf, exact hf,
  exact path_concatenation_continuous_on hw hl1c hl2c,
  exact path_concatenation_deriv_integrable hw hl1i hl2i,
end

/- The integral along the inverse of a path is equal to the negative number of that along the original path. -/
theorem contour_integral_along_inverse_path
{f : ℂ → E} {L:ℝ → ℂ}(hf: continuous f) :
contour_integral f (path_inverse L) = - contour_integral f L :=
begin
  unfold contour_integral,
  unfold path_inverse,
  let h:ℝ → ℝ := λ(t:ℝ ), 1-t,
  let h':ℝ → ℝ :=λ(t:ℝ ), -1,
  have h_def: h = λ(t:ℝ ), 1-t := rfl,
  have h'_def: ∀ x:ℝ , h' x = -1:=congr_fun rfl,
  have h_diff: ∀ x:ℝ, differentiable_at ℝ h x:=
    begin
    intro x,
    simp,
    end,
  have deriv_h_eq_h':  deriv h = h':=
    begin
      ext1,
      rw h'_def x,
      simp, 
    end,
  have p: ∀ x:ℝ , (x ∈ (set.interval (0:ℝ) 1)) → 
    (has_deriv_at h (h' x) x):=
    begin
      intro x,
      intro q,
      rw ← deriv_h_eq_h',
      apply differentiable_at.has_deriv_at (h_diff x), 
    end,
  have q: continuous_on h' (set.interval (0:ℝ) 1):=
    by exact continuous_on_const,
  have Lh:(λ (t:ℝ), L(1-t))=L∘ h:= by simp,
  have L1_minus_t_der': ∀ x:ℝ, 
    deriv ((λ (t:ℝ), L(1-t))) x = (- (deriv L) ∘ h) x:=
    begin
      intro x,
      rw Lh,
      have dcond: (differentiable_at ℝ L (h x)) ∨ 
        ¬ (differentiable_at ℝ L (h x)) := em (differentiable_at ℝ L (h x)),
      cases dcond,
      rw deriv.scomp x (dcond) (h_diff x),
      simp,
      have dlhx: deriv L (h x) = 0 :=deriv_zero_of_not_differentiable_at dcond,
      have dlhx': (-deriv L∘ h)x = 0 :=by {simp,exact dlhx,},
      rw dlhx',
      apply deriv_zero_of_not_differentiable_at,
      intro drlhx,
      have Lhh : L = (L∘ h)∘ h:= by {ext1, rw h_def, simp,},
      have hhx: h (h x) = x:= by {rw h_def,simp,},
      rw Lhh at dcond,
      apply dcond,
      apply differentiable_at.comp,
      rw hhx,
      exact drlhx,
      exact h_diff (h x),
    end, 
  have L1_minus_t_der: 
    deriv ((λ (t:ℝ), L(1-t))) = - (deriv L) ∘ h :=
    begin
      ext1,
      exact L1_minus_t_der' x,
    end, 
  rw L1_minus_t_der,
  simp,
  rw h_def,
  simp,
  let func_lhs: ℝ → E:= λ (x:ℝ), deriv L (1-x) • f(L(1-x)),
  let func_rhs: ℝ → E:=λ (t:ℝ), deriv L t • f (L t),
  have func_lhs_def: func_lhs 
    = λ (t:ℝ), deriv L (1-t) • f(L(1-t)) :=rfl,
  have func_rhs_def: func_rhs
    = λ (t:ℝ), deriv L t • f (L t) := rfl,
  have relation_lr: func_lhs = - h' • (func_rhs ∘ h):=
    begin
      rw func_lhs_def,
      ext1,
      simp,
    end,
  have lhs: ∫ (x : ℝ) in 0..1, deriv L (1 - x) • f (L (1 - x))
    = ∫ (t : ℝ) in 0..1, func_lhs t := by rw func_lhs_def,
  have rhs: ∫ (t : ℝ) in 0..1, deriv L t • f (L t) 
    = ∫ (t : ℝ) in 0..1, func_rhs t := by rw func_rhs_def,
  rw lhs,
  rw rhs,
  rw relation_lr,
  simp,
end
