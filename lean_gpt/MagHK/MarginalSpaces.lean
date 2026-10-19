import MagHK.WeakDifferential
import MagHK.FunctionSpaces
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Tactic.Finiteness

/-! H1 marginal density and current spaces. The external inputs are the
Hilbert-valued Sobolev embedding and the Fubini identification of weak
Sobolev derivatives. The marginal formulas and exponent estimates are proved. -/
noncomputable section
namespace MagHK.MarginalSpaces
open MeasureTheory Set
open scoped ENNReal ComplexConjugate ContDiff
abbrev Space := MagHK.WeakDifferential.Space
abbrev Slice := Lp ℂ 2 (volume : Measure Space)
abbrev Index := Fin 3

def DensitySpace (ρ : Space → ℝ) : Prop := MemLp ρ 1 ∧ MemLp ρ 3
def CurrentSpace (j : Space → ℝ) : Prop := MemLp j 1 ∧ MemLp j (3 / 2)

structure H1Map (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  value : Space → E
  gradient : Index → Space → E
  value_l2 : MemLp value 2
  gradient_l2 : ∀ i, MemLp (gradient i) 2
  weak : ∀ i (η : Space → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
    (∫ x, MagHK.WeakDifferential.dCoord η i x • value x) =
      -(∫ x, η x • gradient i x)

/-- The usual dimension-three Hilbert-valued Sobolev embedding. The type and
map are arbitrary, and no marginal or current is mentioned. -/
def StandardSobolevLibrary : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : H1Map E), MemLp f.value 6

def pairDirection (i : Fin 2) (k : Index) : Space × Space :=
  if i = 0 then (EuclideanSpace.single k 1, 0) else (0, EuclideanSpace.single k 1)

structure H1Wave where
  value : Space × Space → ℂ
  gradient : Fin 2 → Index → Space × Space → ℂ
  value_l2 : MemLp value 2
  gradient_l2 : ∀ i k, MemLp (gradient i k) 2
  weak : ∀ i k (η : Space × Space → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
    (∫ p, (fderiv ℝ η p (pairDirection i k) : ℂ) * value p) =
      -(∫ p, (η p : ℂ) * gradient i k p)

/-- Fubini's unitary L2 identification intertwines the closed gradient
operators in the first variable. This is a general weak-derivative slicing
result for all two-variable H1 functions, with actual representatives. -/
def StandardSlicingLibrary : Prop :=
  ∀ ψ : H1Wave, ∃ f : H1Map Slice,
    (∀ᵐ p : Space × Space, f.value p.1 p.2 = ψ.value p) ∧
    ∀ k, ∀ᵐ p : Space × Space, f.gradient k p.1 p.2 = ψ.gradient 0 k p

def density (ψ : H1Wave) (x : Space) : ℝ :=
  2 * ∫ y, Complex.normSq (ψ.value (x, y))

def paramagneticCurrent (ψ : H1Wave) (k : Index) (x : Space) : ℝ :=
  2 * ∫ y, (conj (ψ.value (x, y)) * ψ.gradient 0 k (x, y)).im

theorem slice_mass (u : Slice) : (∫ y, Complex.normSq (u y)) = ‖u‖ ^ 2 := by
  calc
    _ = ∫ y, inner ℝ (u y) (u y) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        dsimp only
        rw [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq])
    _ = inner ℝ u u := rfl
    _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u

theorem slice_current (u v : Slice) :
    (∫ y, (conj (u y) * v y).im) = (inner ℂ u v).im := by
  have hi : Integrable (fun y => conj (u y) * v y) := by
    simpa only [RCLike.inner_apply'] using L2.integrable_inner (𝕜 := ℂ) u v
  have he : (∫ y, conj (u y) * v y) = inner ℂ u v := by
    simp only [L2.inner_def, RCLike.inner_apply']
  simpa only [he, RCLike.im_eq_complex_im] using (integral_im hi)

theorem density_representation (ψ : H1Wave) (f : H1Map Slice)
    (hf : ∀ᵐ p : Space × Space, f.value p.1 p.2 = ψ.value p) :
    density ψ =ᵐ[volume] fun x => 2 * ‖f.value x‖ ^ 2 := by
  have ha := Measure.ae_ae_of_ae_prod hf
  filter_upwards [ha] with x hx
  unfold density
  rw [← slice_mass]
  congr 1
  apply integral_congr_ae
  exact hx.mono (fun y hy => congrArg Complex.normSq hy.symm)

theorem current_representation (ψ : H1Wave) (f : H1Map Slice) (k : Index)
    (hf : ∀ᵐ p : Space × Space, f.value p.1 p.2 = ψ.value p)
    (hg : ∀ᵐ p : Space × Space, f.gradient k p.1 p.2 = ψ.gradient 0 k p) :
    paramagneticCurrent ψ k =ᵐ[volume]
      fun x => 2 * (inner ℂ (f.value x) (f.gradient k x)).im := by
  have ha := Measure.ae_ae_of_ae_prod hf
  have hb := Measure.ae_ae_of_ae_prod hg
  filter_upwards [ha, hb] with x hx hy
  unfold paramagneticCurrent
  rw [← slice_current]
  congr 1
  apply integral_congr_ae
  filter_upwards [hx, hy] with y hf hg
  rw [hf, hg]

theorem norm_square_memLp {E : Type*} [NormedAddCommGroup E]
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p p q]
    (f : Space → E) (hf : MemLp f p) : MemLp (fun x => ‖f x‖ ^ 2) q := by
  simpa only [pow_two] using hf.norm.mul' hf.norm

theorem inner_im_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (f g : Space → E) (hf : MemLp f p) (hg : MemLp g q) :
    MemLp (fun x => (inner ℂ (f x) (g x)).im) r := by
  have hp : MemLp (fun x => ‖f x‖ * ‖g x‖) r := hg.norm.mul' hf.norm
  apply hp.of_le
  · exact Complex.continuous_im.comp_aestronglyMeasurable
      (continuous_inner.comp_aestronglyMeasurable (hf.1.prodMk hg.1))
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)

theorem density_current_spaces (sobolev : StandardSobolevLibrary)
    (slicing : StandardSlicingLibrary) (ψ : H1Wave) :
    DensitySpace (density ψ) ∧ ∀ k, CurrentSpace (paramagneticCurrent ψ k) := by
  obtain ⟨f, hf, hg⟩ := slicing ψ
  have h6 := sobolev Slice f
  have hd : (3 / 2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  have hρ1 : MemLp (fun x => 2 * ‖f.value x‖ ^ 2) 1 := by
    let : ENNReal.HolderTriple 2 2 1 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
    exact (norm_square_memLp f.value f.value_l2).const_mul 2
  have hρ3 : MemLp (fun x => 2 * ‖f.value x‖ ^ 2) 3 := by
    let : ENNReal.HolderTriple 6 6 3 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
    exact (norm_square_memLp f.value h6).const_mul 2
  have hρ := density_representation ψ f hf
  refine ⟨⟨hρ1.ae_eq hρ.symm, hρ3.ae_eq hρ.symm⟩, ?_⟩
  intro k
  have hj := current_representation ψ f k hf (hg k)
  constructor
  · let : ENNReal.HolderTriple 2 2 1 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
    exact ((inner_im_memLp f.value (f.gradient k) f.value_l2 (f.gradient_l2 k)).const_mul 2).ae_eq hj.symm
  · let : ENNReal.HolderTriple 6 2 (3 / 2) := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
    exact ((inner_im_memLp f.value (f.gradient k) h6 (f.gradient_l2 k)).const_mul 2).ae_eq hj.symm

/-- The corresponding literal one-particle density and paramagnetic current. -/
theorem one_particle_density_current_spaces (sobolev : StandardSobolevLibrary)
    (f : H1Map ℂ) :
    DensitySpace (fun x => Complex.normSq (f.value x)) ∧
    ∀ k, CurrentSpace (fun x => (conj (f.value x) * f.gradient k x).im) := by
  have h₆ := sobolev ℂ f
  have hd : (3 / 2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  constructor
  · constructor
    · let : ENNReal.HolderTriple 2 2 1 := ⟨by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
      simpa only [Complex.normSq_eq_norm_sq] using norm_square_memLp f.value f.value_l2
    · let : ENNReal.HolderTriple 6 6 3 := ⟨by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
      simpa only [Complex.normSq_eq_norm_sq] using norm_square_memLp f.value h₆
  · intro k
    constructor
    · let : ENNReal.HolderTriple 2 2 1 := ⟨by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
      simpa only [RCLike.inner_apply'] using
        inner_im_memLp f.value (f.gradient k) f.value_l2 (f.gradient_l2 k)
    · let : ENNReal.HolderTriple 6 2 (3 / 2) := ⟨by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]⟩
      simpa only [RCLike.inner_apply'] using
        inner_im_memLp f.value (f.gradient k) h₆ (f.gradient_l2 k)

theorem density_mass (ψ : H1Wave) :
    (∫ x, density ψ x) = 2 * ∫ p, Complex.normSq (ψ.value p) := by
  have hi : Integrable (fun p => Complex.normSq (ψ.value p)) := by
    simpa only [Complex.normSq_eq_norm_sq] using ψ.value_l2.integrable_norm_pow (by norm_num : 2 ≠ 0)
  unfold density
  rw [integral_const_mul, ← integral_prod _ hi, ← Measure.volume_eq_prod]

theorem normalized_density_mass (ψ : H1Wave)
    (hn : (∫ p, Complex.normSq (ψ.value p)) = 1) : (∫ x, density ψ x) = 2 := by
  rw [density_mass, hn, mul_one]

/-- Scalar multiplication by an admissible magnetic component is L2 for
an actual weak H1 Hilbert-valued map. -/
theorem h1_multiplier (sobolev : StandardSobolevLibrary)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : H1Map E) (A : Space → ℝ) (hA : FunctionSpaces.SumSpace 3 A volume) :
    MemLp (fun x => A x • f.value x) 2 := by
  have h := FunctionSpaces.scalar_multiplier_l2 (fun x => ‖f.value x‖) A
    f.value_l2.norm (sobolev E f).norm hA
  obtain ⟨a, b, ha, hb, he⟩ := hA
  have hm : AEStronglyMeasurable A := by rw [he]; exact ha.1.add hb.1
  apply (memLp_norm_iff (hm.smul f.value_l2.1)).mp
  change MemLp (fun x => ‖A x • f.value x‖) 2
  simpa only [Pi.mul_apply, norm_smul, Real.norm_eq_abs, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h.norm

theorem h1_magnetic_derivative (sobolev : StandardSobolevLibrary)
    (f : H1Map ℂ) (A : Index → Space → ℝ)
    (hA : ∀ k, FunctionSpaces.SumSpace 3 (A k) volume) (k : Index) :
    MemLp (fun x => -Complex.I * f.gradient k x + A k x • f.value x) 2 :=
  ((f.gradient_l2 k).const_mul (-Complex.I)).add (h1_multiplier sobolev f (A k) (hA k))

theorem h1_magnetic_energy (sobolev : StandardSobolevLibrary)
    (f : H1Map ℂ) (A : Index → Space → ℝ)
    (hA : ∀ k, FunctionSpaces.SumSpace 3 (A k) volume) (k : Index) :
    Integrable (fun x => ‖-Complex.I * f.gradient k x + A k x • f.value x‖ ^ 2) :=
  (h1_magnetic_derivative sobolev f A hA k).integrable_norm_pow (by norm_num : 2 ≠ 0)

/-- The scalar-potential quadratic form is finite on every weak H1 map. -/
theorem h1_scalar_form (sobolev : StandardSobolevLibrary)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : H1Map E) (v : Space → ℝ)
    (hv : FunctionSpaces.SumSpace (3 / 2) v volume) :
    Integrable (fun x => ‖f.value x‖ ^ 2 * v x) := by
  have h₂ : MemLp (fun x => ‖f.value x‖ ^ 2) 1 := by
    let : ENNReal.HolderTriple 2 2 1 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
    exact norm_square_memLp f.value f.value_l2
  have h₆ : MemLp (fun x => ‖f.value x‖ ^ 2) 3 := by
    let : ENNReal.HolderTriple 6 6 3 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
    exact norm_square_memLp f.value (sobolev E f)
  exact FunctionSpaces.scalar_pairing_integrable _ v ⟨h₂, h₆⟩ hv

/-- The actual H1 marginals are compatible with the admitted scalar and
magnetic potential classes, including the physical-current correction. -/
theorem h1_marginal_compatibility (sobolev : StandardSobolevLibrary)
    (slicing : StandardSlicingLibrary)
    (interpolation : FunctionSpaces.StandardInterpolationLibrary Space volume)
    (ψ : H1Wave) (v : Space → ℝ) (A : Index → Space → ℝ)
    (hv : FunctionSpaces.SumSpace (3 / 2) v volume)
    (hA : ∀ k, FunctionSpaces.SumSpace 3 (A k) volume) :
    DensitySpace (density ψ) ∧
    Integrable (density ψ * v) ∧
    (∀ k, CurrentSpace (paramagneticCurrent ψ k)) ∧
    (∀ k, CurrentSpace (density ψ * A k)) ∧
    ∀ k, CurrentSpace (paramagneticCurrent ψ k + density ψ * A k) := by
  obtain ⟨hρ, hj⟩ := density_current_spaces sobolev slicing ψ
  have ha : ∀ k, CurrentSpace (density ψ * A k) := fun k =>
    FunctionSpaces.density_times_potential interpolation _ _ hρ (hA k)
  exact ⟨hρ, FunctionSpaces.scalar_pairing_integrable _ _ hρ hv, hj, ha,
    fun k => ⟨(hj k).1.add (ha k).1, (hj k).2.add (ha k).2⟩⟩

end MagHK.MarginalSpaces
