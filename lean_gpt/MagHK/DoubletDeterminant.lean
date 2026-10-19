import MagHK.MonopoleMultiplet
import MagHK.SeparatedDifferential

/-! A determinant in a common radial doublet has the explicit separated
wavefunction. This is an equality of actual L² representatives. -/
noncomputable section
namespace MagHK.MonopoleSeparation
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial

private theorem linear_combination_representative (u v : State) (f : ℝ → ℂ)
    (hu : ∀ᵐ x ∂chartMeasure, u x = f x.1 * Yplus x.2)
    (hv : ∀ᵐ x ∂chartMeasure, v x = f x.1 * Yminus x.2) (a b : ℂ) :
    ∀ᵐ x ∂chartMeasure, (a • u + b • v : State) x =
      f x.1 * (a * Yplus x.2 + b * Yminus x.2) := by
  filter_upwards [Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u,
    Lp.coeFn_smul b v, hu, hv] with x hadd ha hb hux hvx
  rw [hadd, Pi.add_apply, ha, hb]
  change a * u x + b * v x = _
  rw [hux, hvx]
  ring

theorem determinant_of_common_radial (f : ℝ → ℂ) (u v a b : State)
    (hu : ∀ᵐ x ∂chartMeasure, u x = f x.1 * Yplus x.2)
    (hv : ∀ᵐ x ∂chartMeasure, v x = f x.1 * Yminus x.2)
    (ha : a ∈ Submodule.span ℂ {u, v}) (hb : b ∈ Submodule.span ℂ {u, v}) :
    ∃ c : ℂ, ∀ᵐ p ∂pairMeasure,
      determinant a b p = c * separatedWave f p := by
  obtain ⟨a₀, a₁, rfl⟩ := Submodule.mem_span_pair.mp ha
  obtain ⟨b₀, b₁, rfl⟩ := Submodule.mem_span_pair.mp hb
  let c : ℂ := a₀ * b₁ - a₁ * b₀
  refine ⟨c, ?_⟩
  have hA := linear_combination_representative u v f hu hv a₀ a₁
  have hB := linear_combination_representative u v f hu hv b₀ b₁
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hA,
    Measure.quasiMeasurePreserving_snd.ae hA,
    Measure.quasiMeasurePreserving_fst.ae hB,
    Measure.quasiMeasurePreserving_snd.ae hB] with p ha₀ ha₁ hb₀ hb₁
  dsimp only [determinant, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice]
  rw [ha₀, ha₁, hb₀, hb₁]
  dsimp only [c, separatedWave, angularDet, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice]
  ring

end MagHK.MonopoleSeparation
