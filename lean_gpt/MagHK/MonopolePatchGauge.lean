import MagHK.MonopolePatches
import MagHK.MonopoleHilbert

/-! Actual local azimuthal primitives and north/south connection coefficients.
These are Cartesian differential identities, with no operator-theory premise.
The two coordinate patches cover the overlap away from the polar axis.
-/
noncomputable section
namespace MagHK.MonopolePatchGauge
open MagHK.ConstructionData MagHK.MonopolePatches
open scoped ContDiff

def xCoordinate : Space →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
def yCoordinate : Space →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
def zCoordinate : Space →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ

def dot (v : Space) : Space →L[ℝ] ℝ :=
  v.1.1 • xCoordinate + v.1.2 • yCoordinate + v.2 • zCoordinate

@[simp] theorem dot_apply (v d : Space) :
    dot v d = v.1.1 * d.1.1 + v.1.2 * d.1.2 + v.2 * d.2 := rfl

def azimuthX (p : Space) : ℝ := Real.arctan (p.1.2 / p.1.1)
def azimuthY (p : Space) : ℝ := -Real.arctan (p.1.1 / p.1.2)

theorem azimuthX_smooth : ContDiffOn ℝ ∞ azimuthX {p | p.1.1 ≠ 0} := by
  exact (contDiff_fst.snd.contDiffOn.div contDiff_fst.fst.contDiffOn
    (by intro p hp; exact hp)).arctan

theorem azimuthY_smooth : ContDiffOn ℝ ∞ azimuthY {p | p.1.2 ≠ 0} := by
  exact ((contDiff_fst.fst.contDiffOn.div contDiff_fst.snd.contDiffOn
    (by intro p hp; exact hp)).arctan).neg

theorem azimuthX_hasFDerivAt (p : Space) (hp : p.1.1 ≠ 0) :
    HasFDerivAt azimuthX (dot (azimuthal p)) p := by
  have hq : p.1.1 ^ 2 + p.1.2 ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hp, sq_nonneg p.1.2]
  have hinv := (hasDerivAt_inv hp).comp_hasFDerivAt p (xCoordinate.hasFDerivAt)
  have h := (yCoordinate.hasFDerivAt.mul hinv).arctan
  have hd : (1 / (1 + (yCoordinate p * (xCoordinate p)⁻¹) ^ 2)) •
      (yCoordinate p • (-(p.1.1 ^ 2)⁻¹ • xCoordinate) + (xCoordinate p)⁻¹ • yCoordinate) =
      dot (azimuthal p) := by
    apply ContinuousLinearMap.ext
    intro d
    simp only [dot, xCoordinate, yCoordinate, zCoordinate, azimuthal,
      smul_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    field_simp [hp, hq]
    ring
  simpa only [azimuthX, xCoordinate, yCoordinate, div_eq_mul_inv] using! h.congr_fderiv hd

theorem azimuthY_hasFDerivAt (p : Space) (hp : p.1.2 ≠ 0) :
    HasFDerivAt azimuthY (dot (azimuthal p)) p := by
  have hq : p.1.1 ^ 2 + p.1.2 ^ 2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hp, sq_nonneg p.1.1]
  have hinv := (hasDerivAt_inv hp).comp_hasFDerivAt p (yCoordinate.hasFDerivAt)
  have h := ((xCoordinate.hasFDerivAt.mul hinv).arctan).neg
  have hd : -((1 / (1 + (xCoordinate p * (yCoordinate p)⁻¹) ^ 2)) •
      (xCoordinate p • (-(p.1.2 ^ 2)⁻¹ • yCoordinate) + (yCoordinate p)⁻¹ • xCoordinate)) =
      dot (azimuthal p) := by
    apply ContinuousLinearMap.ext
    intro d
    simp only [dot, xCoordinate, yCoordinate, zCoordinate, azimuthal,
      smul_apply, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    field_simp [hp, hq]
    ring
  simpa only [azimuthY, xCoordinate, yCoordinate, div_eq_mul_inv] using! h.congr_fderiv hd

theorem local_azimuth (p : Space) (hp : p.1 ≠ 0) :
    (p.1.1 ≠ 0 ∧ HasFDerivAt azimuthX (dot (azimuthal p)) p) ∨
    (p.1.2 ≠ 0 ∧ HasFDerivAt azimuthY (dot (azimuthal p)) p) := by
  by_cases hx : p.1.1 = 0
  · have hy : p.1.2 ≠ 0 := by intro hy; exact hp (Prod.ext hx hy)
    exact Or.inr ⟨hy, azimuthY_hasFDerivAt p hy⟩
  · exact Or.inl ⟨hx, azimuthX_hasFDerivAt p hx⟩

theorem patch_difference_primitiveX (g : ℝ) (p : Space) (hp : p.1.1 ≠ 0) :
    HasFDerivAt (fun x => 2 * g * azimuthX x) (dot (north g p - south g p)) p := by
  have hxy : p.1 ≠ 0 := by intro h; exact hp (congrArg Prod.fst h)
  have h := (azimuthX_hasFDerivAt p hp).const_mul (2 * g)
  apply h.congr_fderiv
  rw [patch_difference g p hxy]
  apply ContinuousLinearMap.ext
  intro d
  simp [dot_apply, smul_eq_mul]
  ring

theorem patch_difference_primitiveY (g : ℝ) (p : Space) (hp : p.1.2 ≠ 0) :
    HasFDerivAt (fun x => 2 * g * azimuthY x) (dot (north g p - south g p)) p := by
  have hxy : p.1 ≠ 0 := by intro h; exact hp (congrArg Prod.snd h)
  have h := (azimuthY_hasFDerivAt p hp).const_mul (2 * g)
  apply h.congr_fderiv
  rw [patch_difference g p hxy]
  apply ContinuousLinearMap.ext
  intro d
  simp [dot_apply, smul_eq_mul]
  ring

def azimuthalTangent (p : Space) : Space := ((-p.1.2, p.1.1), 0)

theorem north_contraction (g : ℝ) (p : Space) (hp : p.1 ≠ 0) :
    dot (north g p) (azimuthalTangent p) = g * (1 - p.2 / radius p) := by
  have hq : p.1.1 ^ 2 + p.1.2 ^ 2 ≠ 0 := by
    intro h
    apply hp
    ext <;> dsimp <;> nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
  rw [north_eq_string g p hp, dot_apply]
  simpa [azimuthalTangent] using MagHK.DiracString.azimuthal_component g p hq

theorem south_contraction (g : ℝ) (p : Space) (hp : p.1 ≠ 0) :
    dot (south g p) (azimuthalTangent p) = -g * (1 + p.2 / radius p) := by
  have h := north_contraction g (-p) (by simpa using hp)
  simp only [dot_apply, azimuthalTangent, radius_neg] at h ⊢
  dsimp [south] at h ⊢
  simp only [mul_zero, add_zero] at h ⊢
  rw [neg_div] at h
  linarith

theorem north_chart_coefficient (q : ℤ) (p : Space) (hp : p.1 ≠ 0) :
    dot (north ((q : ℝ) / 2) p) (azimuthalTangent p) =
      MagHK.MonopoleRealization.northCoefficient q (p.2 / radius p) :=
  north_contraction _ p hp

theorem south_chart_coefficient (q : ℤ) (p : Space) (hp : p.1 ≠ 0) :
    dot (south ((q : ℝ) / 2) p) (azimuthalTangent p) =
      MagHK.MonopoleRealization.southCoefficient q (p.2 / radius p) := by
  rw [south_contraction _ p hp]
  unfold MagHK.MonopoleRealization.southCoefficient
  ring

end MagHK.MonopolePatchGauge
