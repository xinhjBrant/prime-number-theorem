import tactic
import analysis.normed_space.basic
import analysis.complex.basic
import analysis.calculus.deriv
import measure_theory.integral.interval_integral
noncomputable theory

section order

variables {α : Type*}[linear_order α]

lemma Ioo_subset_interval {a b :α}:
set.Ioo a b ⊆ set.interval a b :=
set.subset.trans set.Ioo_subset_Icc_self set.Icc_subset_interval

lemma Iio_inter_Icc {a b: α}:
set.Iio b ∩ set.Icc a b = set.Ico a b :=
by {rw subset_antisymm_iff, split,
rw [set.Iio, set.Icc, set.Ico], intros x x_in, 
simp at x_in, simp, split, exact x_in.2.1,
exact x_in.1, rw set.subset_inter_iff, split,
exact set.Ico_subset_Iio_self,
exact set.Ico_subset_Icc_self,} 

end order

section topology

universes u v

variables {α : Type u}{β : Type v}
variables [topological_space α]

-- modified from eventually_nhds_iff
lemma eventually_nhds_eq_iff {a : α} {f g : α → β} :
  (∀ᶠ x in nhds a, f x = g x) ↔ ∃ (t : set α), (∀ x ∈ t, f x = g x) ∧ is_open t ∧ a ∈ t := 
  mem_nhds_iff.trans $ by simp only [set.subset_def, exists_prop, set.mem_set_of_eq]

end topology

section complex

lemma continuous_on_log_of_upper_plane:
  continuous_on complex.log {z : ℂ | 0 ≤ z.im ∧ z≠ 0}:=
begin
  intros z z_in,
  simp at z_in,
  by_cases him:z.im=0,
  by_cases hre:z.re<0,
  {
    apply continuous_within_at.mono,
    exact complex.continuous_within_at_log_of_re_neg_of_im_zero
      hre him,
    simp, intros a a_in_1 a_in_2, exact a_in_1,
  },
  {
    apply continuous_at.continuous_within_at,
    apply continuous_at_clog, 
    left, simp at hre, by_cases z.re=0,
    exfalso, exact z_in.2 (complex.ext h him),
    exact (ne.symm h).lt_of_le hre,
  },
  {
    apply continuous_at.continuous_within_at,
    apply continuous_at_clog, 
    right, exact him,
  },
end

end complex

section integral

variables {E : Type} 
[normed_add_comm_group E] [normed_space ℂ E] [complete_space E] 

lemma interval_integrable_iff_integrable_Ico_of_le {μ:measure_theory.measure ℝ}
{f : ℝ → E} {a b : ℝ} (hab : a ≤ b) [measure_theory.has_no_atoms μ] :
  interval_integrable f μ a b ↔ measure_theory.integrable_on f (set.Ico a b) μ :=
begin
  rw interval_integrable_iff',
  split,
  have hinc: set.interval a b = (set.Ico a b) ∪ {b} := by rw [set.interval_of_le hab, set.Ico_union_right hab],
  rw hinc,
  intro condition,
  exact measure_theory.integrable_on.left_of_union condition,
  intro condition,
  apply integrable_on_Icc_iff_integrable_on_Ioo.2,
  have minab:min a b=a:= by rw [min_eq_left hab],
  have maxab:max a b=b:= by rw [max_eq_right hab],
  rw minab,
  rw maxab,
  cases decidable.em (a = b) with heq hneq,
  {rw [heq, set.Ioo_eq_empty _], simp, simp,},
  {
    have h : a < b := ne.lt_of_le hneq hab,
    have hinc:set.Ico a b= set.Ioo a b ∪ {a} := by rw [←set.Ioo_union_left h],
    rw hinc at condition,
    exact measure_theory.integrable_on.left_of_union condition,
  },
  exact _inst_4,
end

lemma interval_integrable_iff_integrable_Ioo_of_le {μ:measure_theory.measure ℝ}
{f : ℝ → E} {a b : ℝ} (hab : a ≤ b) [measure_theory.has_no_atoms μ] :
  interval_integrable f μ a b ↔ measure_theory.integrable_on f (set.Ioo a b) μ :=
begin
  rw interval_integrable_iff_integrable_Icc_of_le hab,
  exact integrable_on_Icc_iff_integrable_on_Ioo,
  exact _inst_4,
end

lemma integral_congr'''{μ:measure_theory.measure ℝ}{a b : ℝ}
{f g : ℝ → E} (hab : a ≤ b) (h : set.eq_on f g (set.Ioo a b))
[measure_theory.has_no_atoms μ] :
  ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
begin
  repeat {rw interval_integral.integral_of_le hab,},
  repeat {rw measure_theory.set_integral_congr_set_ae
    measure_theory.Ioo_ae_eq_Ioc.symm,},
  exact measure_theory.set_integral_congr measurable_set_Ioo h,
  exact _inst_4, exact _inst_4,
end

lemma integral_congr' {μ:measure_theory.measure ℝ}{a b : ℝ}
{f g : ℝ → E} (hab : a ≤ b) (h : set.eq_on f g (set.Ioc a b)) :
  ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
begin 
let ha : ∫ (x : ℝ) in set.Ioc a b, f x ∂μ = ∫ (x : ℝ) in set.Ioc a b, g x ∂μ := measure_theory.set_integral_congr measurable_set_Ioc h,
  simp [interval_integral, hab],
  simp at ha,
  exact ha,
end

lemma integral_congr''  {a b : ℝ}{f g : ℝ → E}{a b : ℝ} 
(hab : a ≤ b) (h : set.eq_on f g (set.Ico a b)) :
  ∫ x in a..b, f x = ∫ x in a..b, g x :=
begin
  let f' := λ x, f (- x),
  let g' := λ x, g (- x),
  have hf' : (λ x, f (- x))= (λ x, f' x) := by simp,
  have hg' : (λ x, g (- x))= (λ x, g' x) := by simp,
  have h1 : set.eq_on f' g' (set.Ioc (- b) (- a)) := 
    begin
      unfold set.eq_on,
      simp,
      intro x,
      let y := - x,
      have h_ : x = - y := by simp,
      rw h_,
      intros hy1 hy2,
      have hf' : f' (- y) = f y := by simp, 
      have hg' : g' (- y) = g y := by simp, 
      rw [hf', hg'],
      unfold set.eq_on at h,
      have hy1' := (iff.elim_right (mul_lt_mul_right_of_neg neg_one_lt_zero)) hy1,
      simp only [neg_mul_neg,mul_one] at hy1', 
      have hy2' := (iff.elim_right (mul_le_mul_right_of_neg neg_one_lt_zero)) hy2,
      simp only [neg_mul_neg,mul_one] at hy2', 
      have hy : y ∈ set.Ico a b := 
        begin 
          unfold set.Ico, 
          simp,
          exact and.intro hy2' hy1',
        end,
      exact h hy,
    end,
  have hba := (iff.elim_right (mul_le_mul_right_of_neg neg_one_lt_zero)) hab,
  simp only [mul_neg_one] at hba,
  have h2 : ∫ (x : ℝ) in -b..-a, f' x = ∫ (x : ℝ) in -b..-a, g' x := integral_congr' hba h1,
  rw [←hf', ←hg'] at h2,
  rw[interval_integral.integral_comp_neg] at h2,
  rw[interval_integral.integral_comp_neg] at h2,
  simp at h2,
  exact h2,
end

lemma volume_add_right (a : ℝ) :
  measure_theory.measure.map ((+) a) measure_theory.measure_space.volume = 
  measure_theory.measure_space.volume :=
begin
  have t:=real.is_add_left_invariant_real_volume.map_add_left_eq_self,
  exact t a,
end

lemma integrable_comp_add_left {f:ℝ → E}{a b:ℝ}
(hf : interval_integrable f measure_theory.measure_space.volume a b) 
(h : ℝ) :
  interval_integrable (λ x, f (h+x)) measure_theory.measure_space.volume (a-h) (b-h) :=
begin
  rw interval_integrable_iff' at hf ⊢,
  have A : measurable_embedding (λ x, (-h)+x) :=
    measurable_embedding_add_left (-h),
  rw [←volume_add_right (-h), measure_theory.integrable_on, 
      ←measure_theory.integrable_on, measurable_embedding.integrable_on_map_iff A],
  convert hf using 1,
  { ext, simp, },
  { simp,},
end

/- The following codes are from Oliver Nash and Bhavik Mehta. 
See Zulip discussion https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/ae.20measurable.20condition 
-/
lemma interval_integrable_norm_iff {f : ℝ → E} {μ : measure_theory.measure ℝ} {a b : ℝ}
  (hf : measure_theory.ae_strongly_measurable f (μ.restrict (set.interval_oc a b))) :
  interval_integrable (λ t, ∥f t∥) μ a b ↔ interval_integrable f μ a b :=
begin
  simp_rw [interval_integrable_iff, measure_theory.integrable_on],
  exact measure_theory.integrable_norm_iff hf,
end 

lemma smul_continuous_on
{μ : measure_theory.measure ℝ} {a b : ℝ} {f : ℝ → ℂ} {g : ℝ → E}
  (hf : measure_theory.ae_strongly_measurable f (μ.restrict (set.interval_oc a b)))
  (hg : continuous_on g (set.interval a b)) :
  measure_theory.ae_strongly_measurable (λ x, f x • g x) (μ.restrict (set.interval_oc a b)) :=
hf.smul ((hg.mono set.Ioc_subset_Icc_self).ae_strongly_measurable measurable_set_interval_oc)

lemma interval_integrable.smul_continuous_on 
{μ : measure_theory.measure ℝ} {a b : ℝ} {f : ℝ → ℂ} {g : ℝ → E}
  (hf : interval_integrable f μ a b) 
  (hg : continuous_on g (set.interval a b)) :
  interval_integrable (λ x, f x • g x) μ a b :=
begin
have hf' : measure_theory.ae_strongly_measurable (λ (t : ℝ), f t) (μ.restrict (set.interval_oc a b)),
  { -- Missing lemma for `Ioc a b` case.
    rcases le_or_gt a b with h | h,
    { convert hf.ae_strongly_measurable,
      exact set.interval_oc_of_le h, },
    { convert hf.ae_strongly_measurable',
      rw set.interval_oc_swap, -- Missing lemma `interval_oc_of_ge`
      exact set.interval_oc_of_le (le_of_lt h), }, },
  rw ← interval_integrable_norm_iff,
  { simp_rw norm_smul,
    refine interval_integrable.mul_continuous_on _ (continuous_norm.comp_continuous_on hg),
    simp at hf',
    rw interval_integrable_norm_iff hf',
    assumption, },
  exact smul_continuous_on hf' hg,
end

end integral
