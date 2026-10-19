import MagHK.PotentialSpaces
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Sum-space multiplication and the density/current compatibility exponents.
The only background input here is the general Lp interpolation theorem.
All multiplication and square estimates use the literal functions. -/
noncomputable section
namespace MagHK.FunctionSpaces
open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def SumSpace {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) (f : X → E) (μ : Measure X) : Prop :=
  ∃ u v : X → E, MemLp u p μ ∧ MemLp v ∞ μ ∧ f = u + v

def Intersection {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (f : X → E) (μ : Measure X) : Prop := MemLp f 1 μ ∧ MemLp f p μ

theorem SumSpace.add {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    {f g : X → E} (hf : SumSpace p f μ) (hg : SumSpace p g μ) :
    SumSpace p (f + g) μ := by
  obtain ⟨f₁, f₂, hf₁, hf₂, rfl⟩ := hf
  obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := hg
  exact ⟨f₁ + g₁, f₂ + g₂, hf₁.add hg₁, hf₂.add hg₂, by abel⟩

theorem SumSpace.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}
    {f : X → E} (hf : SumSpace p f μ) (T : E →L[ℝ] F) :
    SumSpace p (T ∘ f) μ := by
  obtain ⟨f₁, f₂, hf₁, hf₂, rfl⟩ := hf
  exact ⟨T ∘ f₁, T ∘ f₂, T.comp_memLp' hf₁, T.comp_memLp' hf₂,
    by ext x; exact map_add T _ _⟩

def StandardInterpolationLibrary (X : Type*) [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ (p q r : ℝ≥0∞) (f : X → ℝ), 0 < p → p ≤ r → r ≤ q →
    MemLp f p μ → MemLp f q μ → MemLp f r μ

private theorem holder_three : ENNReal.HolderTriple 3 3 (3 / 2) := by
  have hd : (3 / 2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

private theorem holder_three_half : ENNReal.HolderTriple (3 / 2) 3 1 := by
  have hd : (3 / 2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem density_times_potential
    (interpolation : StandardInterpolationLibrary X μ)
    (ρ A : X → ℝ) (hρ : Intersection 3 ρ μ) (hA : SumSpace 3 A μ) :
    Intersection (3 / 2) (ρ * A) μ := by
  obtain ⟨f, g, hf, hg, rfl⟩ := hA
  have hmiddle : MemLp ρ (3 / 2) μ :=
    interpolation 1 3 (3 / 2) ρ (by norm_num)
      (by apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num)
      (by apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num)
      hρ.1 hρ.2
  have hfirst : MemLp (ρ * f) 1 μ := by
    letI := holder_three_half
    exact hf.mul hmiddle
  have hsecond : MemLp (ρ * f) (3 / 2) μ := by
    letI := holder_three
    exact hf.mul hρ.2
  constructor
  · simpa only [mul_add, mul_comm g ρ] using hfirst.add (hρ.1.mul hg)
  · simpa only [mul_add, mul_comm g ρ] using hsecond.add (hmiddle.mul hg)

theorem scalar_pairing_integrable (ρ v : X → ℝ)
    (hρ : Intersection 3 ρ μ) (hv : SumSpace (3 / 2) v μ) :
    Integrable (ρ * v) μ := by
  obtain ⟨f, g, hf, hg, rfl⟩ := hv
  letI := holder_three_half
  have h : MemLp (ρ * f) 1 μ := hf.mul hρ.2
  exact (memLp_one_iff_integrable.mp
    (by simpa only [mul_add, mul_comm g ρ] using h.add (hρ.1.mul hg)))

theorem scalar_multiplier_l2 (u A : X → ℝ)
    (hu₂ : MemLp u 2 μ) (hu₆ : MemLp u 6 μ) (hA : SumSpace 3 A μ) :
    MemLp (A * u) 2 μ := by
  obtain ⟨f, g, hf, hg, rfl⟩ := hA
  letI : ENNReal.HolderTriple 3 6 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
  simpa only [add_mul] using (hu₆.mul hf).add (hu₂.mul hg)

theorem sum_space_square {E : Type*} [NormedAddCommGroup E]
    (A : X → E) (hA : SumSpace 3 A μ) :
    SumSpace (3 / 2) (fun x => ‖A x‖ ^ 2) μ := by
  obtain ⟨f, g, hf, hg, hAeq⟩ := hA
  have htop : eLpNormEssSup g μ < ∞ := by
    simpa only [eLpNorm_exponent_top] using hg.2
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  have hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ (B : ℝ) := by
    filter_upwards [hB] with x hx
    exact_mod_cast hx
  let s : Set X := {x | 1 < ‖f x‖}
  have hs : NullMeasurableSet s μ :=
    nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable
  have hnorm : AEStronglyMeasurable (fun x => ‖A x‖ ^ 2) μ := by
    rw [hAeq]
    exact (hf.1.add hg.1).norm.pow 2
  have hlarge : MemLp (s.indicator (fun x => ‖A x‖ ^ 2)) (3 / 2) μ := by
    letI := holder_three
    have hsq : MemLp (fun x => ‖f x‖ ^ 2) (3 / 2) μ := by
      simpa only [pow_two] using hf.norm.mul' hf.norm
    apply hsq.of_le_mul (c := (1 + (B : ℝ)) ^ 2) (hnorm.indicator₀ hs)
    filter_upwards [hb] with x hgx
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ha : ‖A x‖ ≤ ‖f x‖ + B := by
        rw [hAeq, Pi.add_apply]
        exact (norm_add_le _ _).trans (add_le_add le_rfl hgx)
      have hx' : 1 < ‖f x‖ := hx
      have hbig : ‖A x‖ ≤ (1 + (B : ℝ)) * ‖f x‖ := by
        nlinarith [B.coe_nonneg]
      calc
        ‖A x‖ ^ 2 ≤ ((1 + (B : ℝ)) * ‖f x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hbig 2
        _ = _ := by ring
    · simp only [indicator_of_notMem hx, norm_zero]
      positivity
  have hsmall : MemLp (sᶜ.indicator (fun x => ‖A x‖ ^ 2)) ∞ μ := by
    apply memLp_top_of_bound (hnorm.indicator₀ hs.compl) ((1 + (B : ℝ)) ^ 2)
    filter_upwards [hb] with x hgx
    by_cases hx : x ∈ sᶜ
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hx' : ‖f x‖ ≤ 1 := le_of_not_gt hx
      have ha : ‖A x‖ ≤ 1 + B := by
        rw [hAeq, Pi.add_apply]
        exact (norm_add_le _ _).trans (add_le_add hx' hgx)
      nlinarith [norm_nonneg (A x), B.coe_nonneg]
    · simp only [indicator_of_notMem hx, norm_zero]
      positivity
  refine ⟨_, _, hlarge, hsmall, ?_⟩
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem scalar_sum_iff (v : MagHK.ConstructionData.Space → ℝ) :
    SumSpace (3 / 2) v volume ↔ MagHK.PotentialSpaces.ScalarSumSpace v := by
  constructor
  · rintro ⟨f, g, hf, hg, h⟩
    exact ⟨f, g, hf, hg, fun x => congrFun h x⟩
  · rintro ⟨f, g, hf, hg, h⟩
    exact ⟨f, g, hf, hg, funext h⟩

theorem vector_norm_square (A : MagHK.ConstructionData.Space → MagHK.ConstructionData.Space)
    (hA : MagHK.PotentialSpaces.VectorSumSpace A) :
    MagHK.PotentialSpaces.ScalarSumSpace (fun x => ‖A x‖ ^ 2) := by
  obtain ⟨f, g, hf, hg, he⟩ := hA
  exact (scalar_sum_iff _).mp (sum_space_square A ⟨f, g, hf, hg, funext he⟩)

/-- The literal Cartesian Euclidean squared magnitude, independently of the
equivalent product norm used to define the vector Lp space. -/
theorem vector_euclidean_square
    (A : MagHK.ConstructionData.Space → MagHK.ConstructionData.Space)
    (hA : MagHK.PotentialSpaces.VectorSumSpace A) :
    MagHK.PotentialSpaces.ScalarSumSpace
      (fun x => (A x).1.1 ^ 2 + (A x).1.2 ^ 2 + (A x).2 ^ 2) := by
  obtain ⟨f, g, hf, hg, he⟩ := hA
  have ha : SumSpace 3 A volume := ⟨f, g, hf, hg, funext he⟩
  let T₁ : MagHK.ConstructionData.Space →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let T₂ : MagHK.ConstructionData.Space →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let T₃ : MagHK.ConstructionData.Space →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have h₁ := sum_space_square (T₁ ∘ A) (ha.map T₁)
  have h₂ := sum_space_square (T₂ ∘ A) (ha.map T₂)
  have h₃ := sum_space_square (T₃ ∘ A) (ha.map T₃)
  apply (scalar_sum_iff _).mp
  change SumSpace (3 / 2)
    (((fun x => (A x).1.1 ^ 2) + fun x => (A x).1.2 ^ 2) + fun x => (A x).2 ^ 2) volume
  simpa only [T₁, T₂, T₃, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Pi.add_apply, Real.norm_eq_abs, sq_abs] using (h₁.add h₂).add h₃

end MagHK.FunctionSpaces
