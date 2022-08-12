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
[normed_group E] [normed_space ℂ E] [complete_space E] 

/-- Before everything: Convert types -/
lemma smul_type_convert (a:ℝ)(b:E):
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

/-- Part I. Define paths and relevant basic operations -/

/- ! We define the path as a differentiable function f : ℝ → ℂ with a continuous derivative,
 defined on ℝ but we only use their value on [0,1]. -/

def constant_path (z:ℂ):ℝ → ℂ :=λ (t:ℝ ), z 

/-- The path concatenation of two path means compressing their domain [0,1] to [0, 1/2] (and [1/2, 1]) then concate them back to [0,1].-/
def path_concatenation {L1:ℝ → ℂ}{L2:ℝ →ℂ}
(hw: L1 1=L2 0):ℝ → ℂ :=
λ (t:ℝ), if t<1/2 then L1 (2*t) else L2 (-1+2*t)

/- The inverse of a path is to reverse the direction of a path. -/
def path_inverse(L:ℝ → ℂ):ℝ → ℂ := λ (t:ℝ ), L(1-t) 

lemma path_concatenation_left{L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0){t:ℝ}(ht: t<=2⁻¹):
path_concatenation hw t = L1 (2*t):=
begin
  by_cases t<1/2,
  rw path_concatenation,
  simp,
  intro p,
  exfalso,
  have hn:¬ t<1/2:=by {simp,exact p},
  exact hn h,
  simp at *,
  have hh: t=2⁻¹:=by {exact ge_antisymm h ht},
  rw hh,
  rw path_concatenation,
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
(hw: L1 1=L2 0):set.eq_on 
((λ t:ℝ, path_concatenation hw t):ℝ → ℂ)
((λ t:ℝ, L1 (2*t)):ℝ → ℂ) (set.interval (0:ℝ) (1/2)):=
begin
  rw set.eq_on,
  intro x,
  intro in_condition,
  simp at in_condition,
  exact path_concatenation_left hw in_condition.2,
end

lemma frac_1_2 : (1 / 2 : ℝ) ≤ 1 := 
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
    simp,
    exact h4,
  end

lemma frac_1_2' : (1 / 2 : ℝ) = (min (1 / 2) 1 : ℝ) := 
  begin
    unfold min,
    unfold min_default,
    rw if_pos frac_1_2,
  end

lemma path_concatenation_endpoint {L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0): path_concatenation hw 1=L2 1:=
begin
  rw path_concatenation,
  have p:=frac_1_2,
  simp at p,
  have m:¬ (1<(1 / 2 : ℝ)):=by {simp,exact p,},
  ring_nf,
  simp,
  intro f,
  exfalso,
  finish,
end

lemma path_concatenation_right'{L1:ℝ → ℂ}{L2:ℝ→ℂ}
(hw: L1 1=L2 0):set.eq_on 
((λ t:ℝ, path_concatenation hw t):ℝ → ℂ)
((λ t:ℝ, L2 (-1+2*t)):ℝ → ℂ) (set.interval (1/2) (1:ℝ)):=
begin
  rw set.eq_on,
  intro x,
  intro in_condition,
  apply path_concatenation_right,
  rw[ge],
  rw set.interval at in_condition,
  have h0 : (min (1 / 2) 1 : ℝ) ≤ x := and.elim_left ((iff.elim_left set.mem_Icc) in_condition),
  have h1 : min (1 / 2) 1 = 1 / 2 := rfl,
  have h4 : 2⁻¹ ≤ x := 
    calc 2⁻¹ = (1 / 2 : ℝ) : by ring
    ... = (min (1 / 2) 1 : ℝ) : by rw ←frac_1_2'
    ... ≤ x : h0,
  exact h4,
end

lemma continuity_of_constant_path (z:ℂ): continuous (constant_path z):=
begin
  rw constant_path,
  exact continuous_const,
end

lemma path_concatenation_integrable{L1:ℝ→ ℂ}{L2:ℝ → ℂ}(hw: L1 1=L2 0)
(hl1:interval_integrable (deriv L1) measure_theory.measure_space.volume 0 1)
(hl2:interval_integrable (deriv L2) measure_theory.measure_space.volume 0 1):
  interval_integrable (deriv (path_concatenation hw)) 
  measure_theory.measure_space.volume 0 1 :=
begin
  sorry,
end

/-- Part II. Define contour integral -/

def contour_integral (f : ℂ → E) (L: ℝ → ℂ): E :=
∫ (t: ℝ ) in 0..1, (deriv L t) • f(L t) 

/-- Part III. Integrals along path with operations -/

@[simp] lemma integral_along_constant_path 
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

/- The integral using affine change of variables -/
lemma affine_change_of_variable_pre (k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ)
(f : ℂ → E)(L:ℝ → ℂ)
(hf: continuous f)(hld: differentiable ℝ L)
(hl: continuous (deriv L)):
∫ (x : ℝ) in lep..rep, ((constant_real_function k) x) • 
(deriv L ((affine_function k b) x) • 
f (L ((affine_function k b) x)))
= ∫ (t : ℝ) in ((affine_function k b) lep)..
  ((affine_function k b) rep), 
  deriv L t • f (L t) :=
begin
  let func_lhs: ℝ → E:= λ (x:ℝ), 
    deriv L ((affine_function k b) x) • 
      f (L ((affine_function k b) x)),
  let func_rhs: ℝ → E:=λ (t:ℝ), deriv L t • f (L t),
  have func_lhs_def: func_lhs = λ (x:ℝ), 
    deriv L ((affine_function k b) x) • 
      f (L ((affine_function k b) x)) :=rfl,
  have func_rhs_def: func_rhs
    = λ (t:ℝ), deriv L t • f (L t) := rfl,
  have func_rhs_def': func_rhs 
    = deriv L • (f∘ L) := rfl,
  have relation_lr: func_lhs =  
    func_rhs ∘ (affine_function k b):= by rw func_lhs_def,
  have lhs: ∫ (x : ℝ) in lep..rep, 
    ((constant_real_function k) x) • 
    deriv L (affine_function k b x) 
    • f (L (affine_function k b x))
    = ∫ (t : ℝ) in lep..rep, 
    ((constant_real_function k) t) • func_lhs t := 
    by rw func_lhs_def,
  have rhs: ∫ (t : ℝ) in ((affine_function k b) lep)..
  ((affine_function k b) rep), 
    deriv L t • f (L t) 
    = ∫ (t : ℝ) in ((affine_function k b) lep)..
  ((affine_function k b) rep), 
    func_rhs t := by rw func_rhs_def,
  rw lhs,
  rw rhs, 
  rw relation_lr,
  have lcont: continuous L := 
    by exact differentiable.continuous hld,
  have flcont: continuous (f ∘ L):= continuous.comp hf lcont,
  have rc: continuous func_rhs:=
    begin
      rw func_rhs_def,
      exact continuous.smul hl flcont,
    end,
  simp,
  rw interval_integral.integral_comp_smul_deriv 
    (affine_has_deriv_on_interval k b lep rep)
    (affine_in_C1_on_interval k lep rep) rc,
end

lemma affine_change_of_variable (k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ)
(f : ℂ → E)(L:ℝ → ℂ)
(hf: continuous f)(hld: differentiable ℝ L)
(hl: continuous (deriv L)):
k • ∫ (t : ℝ) in lep..rep, (deriv L (b+k*t) • f (L (b+k*t)))
= ∫ (t : ℝ) in (b+k*lep)..(b+k*rep), deriv L t • f (L t) :=
begin
  have p:=affine_change_of_variable_pre k b lep rep f L hf hld hl,
  rw constant_real_function at p,
  rw affine_function at p,
  simp at p,
  exact p,
end

lemma affine_change_of_variable' (k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ)
(f : ℂ → E)(L:ℝ → ℂ)
(hf: continuous f)(hld: differentiable ℝ L)
(hl: continuous (deriv L)):
∫ (t : ℝ) in lep..rep,  (deriv (L ∘ (affine_function k b)) t) 
• f (L ((affine_function k b) t))
= ∫ (t : ℝ) in (b+k*lep)..(b+k*rep), 
  deriv L t • f (L t) :=
begin
  rw ← affine_change_of_variable k b lep rep f L hf hld hl,
  rw deriv_of_path_affine_comp k b L,
  rw affine_function,
  simp,
  have rhs1: k • ∫ (t : ℝ) in lep..rep, deriv L (b + k * t) • f (L (b + k * t))
  = ∫ (t : ℝ) in lep..rep, k• (deriv L (b + k * t) • f (L (b + k * t))):= 
  by simp,
  rw rhs1,
  have im1:  ∀ t:ℝ, ((k:ℂ) * deriv L (b + k * t)) • f (L (b + k * t))
  =(k:ℂ) • (deriv L (b + k * t) • f (L (b + k * t))):=
  begin
    intro t,
    rw mul_smul,
  end,
  have im2:  ∀ t:ℝ, (k:ℂ) • (deriv L (b + k * t) • f (L (b + k * t)))
  =k • (deriv L (b + k * t) • f (L (b + k * t))):=
  by simp,
  have im3: ((λ t:ℝ, ((k:ℂ) * deriv L (b + k * t)) • f (L (b + k * t))):ℝ → E)
  =((λ t:ℝ, k • (deriv L (b + k * t) • f (L (b + k * t)))):ℝ → E):=
  by {ext1,rw im1 x,rw im2 x},
  rw im3,
end

lemma genearl_term_of_sum' (f : ℂ → E)(L:ℝ → ℂ)
(k:ℝ)(b:ℝ)(lep:ℝ)(rep:ℝ):
∫ (t : ℝ) in b+k*lep..b+k*rep, deriv L t • f (L t) 
= ∫ (t : ℝ) in lep..rep, 
deriv (L ∘ (affine_function k b)) t • f (L (b+k*t)):=
begin
  rw deriv_of_path_affine_comp,
  rw ← interval_integral.smul_integral_comp_add_mul _ k b,
  rw affine_function,
  simp,
  have p1: (λ t:ℝ, (↑k * deriv L (b + k * t)) • 
  f (L (b + k * t))) = (λ t:ℝ, 
  ↑k •  deriv L (b + k * t) • f (L (b + k * t))):=
    by {ext1, rw smul_assoc_convert,},
  rw p1,
  rw ← smul_integral_convert,
  simp,
end

lemma genearl_term_of_sum (f : ℂ → E)(L:ℝ → ℂ)
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

lemma first_term_of_sum(f : ℂ → E)(L1:ℝ → ℂ): 
∫ (t : ℝ) in 0..1, deriv L1 t • f (L1 t) 
= ∫ (t : ℝ) in 0..1/2, 
deriv (λ(t:ℝ),L1 (2*t)) t • f (L1 (2*t)) :=
begin
  have p:(λ t:ℝ,deriv (λ(x:ℝ),L1 (2*x)) t • f (L1 (2*t)))
  =(λ t:ℝ,deriv (λ(x:ℝ),L1 (0+2*x)) t • f (L1 (0+2*t))) := 
    by simp,
  rw p,
  rw ← genearl_term_of_sum f L1 2 0 0 (1/2),
  simp,
end

lemma second_term_of_sum(f : ℂ → E)(L2:ℝ → ℂ): 
∫ (t : ℝ) in 0..1, deriv L2 t • f (L2 t) 
= ∫ (t : ℝ) in (1/2)..1, 
deriv (λ(t:ℝ),L2 (-1+2*t)) t • f (L2 (-1+2*t)) :=
begin
  rw ← genearl_term_of_sum f L2 2 (-1) (1/2) 1,
  simp,
  have q: (-1)+2 = (1:ℝ) :=by ring,
  rw q,
end

lemma con_lemma : differentiable ℝ (λ (x : ℝ), -1 + 2 * x) :=
begin
  intro x,
  simp,
end

/- The integral along the path L1∪L2 is equal to the sum of integrals along L1 and L2. -/
lemma integral_along_piecewise_path{f : ℂ → E}
{L1:ℝ → ℂ}{L2:ℝ → ℂ} (hw: L1 1=L2 0) (hf: continuous f)
(hld1: differentiable ℝ L1)(hl1: continuous (deriv L1))
(hld2: differentiable ℝ L2)(hl2: continuous (deriv L2)) :
contour_integral f (path_concatenation hw) = 
contour_integral f L1 + contour_integral f L2 :=
begin
  unfold contour_integral,

  have l1_cont: continuous L1 := 
    by exact differentiable.continuous hld1,
  have l1_cont': continuous (λ (t : ℝ), L1 (2 * t)) := 
    begin
      apply continuous.comp l1_cont,
      have diff : differentiable ℝ (λ (x : ℝ), 2 * x) := begin intro x, simp, end,
      exact differentiable.continuous diff,
    end,
  have fl1_cont: continuous (f ∘ (λ (t : ℝ), L1 (2 * t))) := 
    by exact continuous.comp hf l1_cont',
  have l1d:(λ (t : ℝ), L1 (2 * t))=L1∘ (affine_function 2 0):=
    by {ext1, rw affine_function, simp,},
  let af2:=affine_function 2 0,
  have af2_def:af2=affine_function 2 0:=rfl,
  have af2_diff:∀x:ℝ, differentiable_at ℝ af2 x:=
    by {rw af2_def, intro x, exact (affine_is_differentiable 2 0) x,},
  have hh₂:∀ x:ℝ, differentiable_at ℝ L1 (af2 x):=
    begin
      intro x,
      rw af2_def,
      rw affine_function,
      simp,
      rw differentiable at hld1,
      exact hld1 (2*x),
    end, 
  have deriv_L1d:  ∀ x:ℝ, (deriv (λ (t : ℝ), L1 (2 * t)) x)=
  (deriv af2 x) • (deriv L1 (af2 x)) :=
    begin
      rw l1d,
      intro x,
      exact deriv.scomp x (hh₂ x) (af2_diff x),
    end,
  have deriv_L1d': (deriv (λ (t : ℝ), L1 (2 * t)))=
  2 * ((deriv L1)∘ af2) :=
    begin
      ext1,
      simp,
      rw deriv_L1d x,
      rw af2_def,
      rw deriv_of_affine 2 0,
      rw constant_real_function,
      simp,
    end,
  let af2c:ℂ → ℂ :=λz,(2*z),
  have af2c_def: (af2c= (( λ (z:ℂ), (2 * z)):ℂ → ℂ)):=by simp,
  have af2c_cont: continuous af2c:=by {rw af2c_def,exact continuous_mul_left 2,},
  have hl1'_pre: continuous ((deriv L1) ∘ af2):=
    begin
      rw af2_def,
      exact continuous.comp hl1 (affine_is_continuous 2 0),
    end,
  have deriv_L1d'':(deriv (λ (t : ℝ), L1 (2 * t)))=
  af2c ∘  ((deriv L1)∘ af2):= by {rw af2c_def,rw deriv_L1d', ring_nf,},
  have hl1' : continuous (deriv (λ (t : ℝ), L1 (2 * t))) := 
  begin
    rw deriv_L1d'',
    exact continuous.comp af2c_cont hl1'_pre,
  end,
  have first_cont: continuous 
    ((λ (t : ℝ), deriv (λ (t : ℝ), L1 (2 * t)) t • f (L1 (2 * t))):ℝ → E ):= 
    by exact continuous.smul hl1' fl1_cont,
  have first_integrable_l : interval_integrable 
    ((λ (t : ℝ), deriv (λ (t : ℝ), L1 (2 * t)) t • f (L1 (2 * t))) :ℝ → E ) 
    measure_theory.measure_space.volume 0 (1/2):=
    continuous.interval_integrable first_cont 0 (1/2),

  have first_func : ∀ (t:ℝ), t ∈ (set.Ico (0:ℝ) (1/2)) → 
  deriv (λ(t:ℝ),L1 (2*t)) t • f (L1 (2*t)) = deriv (path_concatenation hw) t • 
    f (path_concatenation hw t) :=
  begin
    intro t,
    intro in_condition,
    simp at in_condition,
    repeat {rw path_concatenation_left hw in_condition.2,},
    have h1 : deriv (path_concatenation hw) t = deriv (λ (t : ℝ), L1 (2 * t)) t := 
      begin 
        apply filter.eventually_eq.deriv_eq,
        unfold filter.eventually_eq,
        apply iff.elim_right eventually_nhds_eq_iff,
        existsi {x : ℝ | x < 2⁻¹},
        apply and.intro,
        {
          intros x hx,
          simp at hx,
          have h0 : x ≤ 2⁻¹ :=  has_lt.lt.le hx,
          exact path_concatenation_left hw h0,
        },
        {
          apply and.intro,
          {
            exact is_open_Iio,
          },
          {
            simp,
            exact in_condition.right,
          }
        }
      end,
    rw h1,
    have ht := has_lt.lt.le in_condition.right,
    rw path_concatenation_left hw ht,
  end,

  have first_func' : set.eq_on ((λ x :ℝ, deriv (λ(t:ℝ),L1 (2*t)) x • f (L1 (2 * x))):ℝ→ E)
  ((λ x :ℝ, deriv (path_concatenation hw) x • f (path_concatenation hw x)):ℝ → E) 
  (set.Ico (0:ℝ) (1/2:ℝ)):=
    by {rw set.eq_on, exact first_func,},

  have l2d:(λ (t : ℝ), L2 (-1 + 2 * t))=L2∘ (affine_function 2 (-1)):=
    by {ext1, rw affine_function,},
  let af21:=affine_function 2 (-1),
  have af21_def:af21=affine_function 2 (-1):=rfl,
  have af21_diff:∀x:ℝ, differentiable_at ℝ af21 x:=
    by {rw af21_def, intro x, exact (affine_is_differentiable 2 (-1)) x,},
  have hh₃:∀ x:ℝ, differentiable_at ℝ L2 (af21 x):=
    begin
      intro x,
      rw af21_def,
      rw affine_function,
      simp,
      rw differentiable at hld2,
      exact hld2 (-1+2*x),
    end, 
  have deriv_L2d:  ∀ x:ℝ, (deriv (λ (t : ℝ), L2 (-1 + 2 * t)) x)=
  (deriv af21 x) • (deriv L2 (af21 x)) :=
    begin
      rw l2d,
      intro x,
      exact deriv.scomp x (hh₃ x) (af21_diff x),
    end,
  have deriv_L2d': (deriv (λ (t : ℝ), L2 (-1 + 2 * t)))=
  2 * ((deriv L2)∘ af21) :=
    begin
      ext1,
      simp,
      rw deriv_L2d x,
      rw af21_def,
      rw deriv_of_affine 2 (-1),
      rw constant_real_function,
      simp,
    end,
  have hl2'_pre: continuous ((deriv L2) ∘ af21):=
    begin
      rw af21_def,
      exact continuous.comp hl2 (affine_is_continuous 2 (-1)),
    end,
  have deriv_L2d'':(deriv (λ (t : ℝ), L2 (-1 + 2 * t)))=
  af2c ∘  ((deriv L2)∘ af21):= by {rw af2c_def,rw deriv_L2d', ring_nf,},
  have hl2' : continuous (deriv (λ (t : ℝ), L2 (-1 + 2 * t))) := 
    begin
    rw deriv_L2d'',
    exact continuous.comp af2c_cont hl2'_pre,
    end,

  have second_func:∀ (t:ℝ), t∈ (set.Ioc (1/2:ℝ) (1:ℝ))→ 
  deriv (λ(t:ℝ),L2 (-1+2*t)) t • f (L2 (-1+2*t)) = deriv (path_concatenation hw) t • f (path_concatenation hw t) :=
  begin
    intro t,
    intro in_condition,
    simp at in_condition,
    repeat {rw path_concatenation_left hw in_condition.2,},
    have h1 : deriv (path_concatenation hw) t = deriv (λ (t : ℝ), L2 (-1 + 2 * t)) t := 
      begin 
        apply filter.eventually_eq.deriv_eq,
        unfold filter.eventually_eq,
        apply iff.elim_right eventually_nhds_eq_iff,
        existsi {x : ℝ | x > 2⁻¹},
        apply and.intro,
        {
          intros x hx,
          simp at hx,
          have h0 : x ≥ 2⁻¹ :=  has_lt.lt.le hx,
          exact path_concatenation_right hw h0,
        },
        {
          apply and.intro,
          {
            exact is_open_Ioi,
          },
          {
            simp,
            exact in_condition.left,
          }
        }
      end,
    rw h1,
    have ht := has_lt.lt.le in_condition.left,
    rw path_concatenation_right hw ht,
  end,

  have second_func':set.eq_on ((λ t:ℝ,deriv (λ(t:ℝ),L2 (-1+2*t)) t • f (L2 (-1+2*t)) ):ℝ → E) ((λt:ℝ, deriv (path_concatenation hw) t • f (path_concatenation hw t)):ℝ→ E) 
  (set.Ioc (1/2:ℝ) (1:ℝ)):=
    by {rw set.eq_on,exact second_func,},
  
  have h_ : (0:ℝ) ≤ (1/2:ℝ) := by simp,

  --have first_integrable : integrable ((λ(t:ℝ), (deriv L1 t)• f(L1(t))):ℝ → E ) (μ.restrict set.Ioc 0 (1 / 2))

  have lhs: 
    (∫ (t : ℝ) in 0..1/2, deriv (path_concatenation hw) t • f (path_concatenation hw t) ) 
    +
    (∫ (t : ℝ) in 1/2..1, deriv (path_concatenation hw) t • f (path_concatenation hw t) ) 
    =
    ∫ (t : ℝ) in 0..1, deriv (path_concatenation hw) t • f (path_concatenation hw t) 
    :=
  begin
    apply interval_integral.integral_add_adjacent_intervals,
    {
      apply iff.elim_right (interval_integrable_iff_integrable_Ico_of_le h_),
      have h : measure_theory.integrable_on (λ (t : ℝ), deriv (λ (t : ℝ), L1 (2 * t)) t • f (L1 (2*t))) (set.Ico 0 (1 / 2)) measure_theory.measure_space.volume := iff.elim_left (interval_integrable_iff_integrable_Ico_of_le h_) first_integrable_l,
      apply measure_theory.integrable_on.congr_fun h first_func' _,
      simp,
      exact _inst_2,
      exact _inst_3,
      exact real.has_no_atoms_volume,
    },
    {
      apply iff.elim_right (interval_integrable_iff_integrable_Ioc_of_le frac_1_2),
      have h : measure_theory.integrable_on (λ (t : ℝ), deriv (λ (t : ℝ), L2 (-1+2*t)) t • f (L2 (-1+2*t))) (set.Ioc (1 / 2) 1) measure_theory.measure_space.volume := 
      begin
        apply iff.elim_left (interval_integrable_iff_integrable_Ioc_of_le frac_1_2),
        apply continuous.interval_integrable,
        apply continuous.smul,
        {
          apply continuous.comp,
          {
            exact hl2',
          },
          {
            have diff : differentiable ℝ (λ (x : ℝ), x) := begin intro x, simp, end,
            exact differentiable.continuous diff,
          }
        },
        {
          apply continuous.comp hf,
          {
            have l2_cont: continuous L2 := by exact differentiable.continuous hld2,
            apply continuous.comp l2_cont,
            have diff : differentiable ℝ (λ (x : ℝ), -1 + 2 * x) :=
            begin intro x, simp, end,
            exact differentiable.continuous diff,
          }
        }      
      end,
      apply measure_theory.integrable_on.congr_fun h second_func' _,
      exact measurable_set_Ioc,
    }
  end,

  rw ←lhs,
  have integral_of_first_func: ∫ (t : ℝ) in 0..1 / 2, 
  deriv (path_concatenation hw) t • 
  f (path_concatenation hw t) = ∫ (t : ℝ) in 0..(1/2), 
  deriv (λ(t:ℝ),L1 (2*t)) t • f (L1 (2*t)):=
    by {rw integral_congr'' h_ first_func',exact real.pi,exact real.pi,},

  have integral_of_second_func: ∫ (t : ℝ) in (1/2)..1, 
  deriv (path_concatenation hw) t • 
  f (path_concatenation hw t) = ∫ (t : ℝ) in (1/2)..1, 
  deriv (λ(t:ℝ),L2 (-1+2*t)) t • f (L2 (-1+2*t)):=
    by rw integral_congr' frac_1_2 second_func',
  rw integral_of_first_func,
  rw integral_of_second_func,
  rw ← first_term_of_sum f L1,
  rw ← second_term_of_sum f L2,
end

/- The integral along the inverse of a path is equal to the negative number of that along the original path. -/
lemma integral_along_inverse_path
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

/-- Part IV. Integrals of functions with basic operations -/
@[simp] lemma integral_of_zero (L:ℝ → ℂ):
contour_integral (λt:ℂ, (0:E)) L = 0 :=
  by { rw contour_integral, simp, }
