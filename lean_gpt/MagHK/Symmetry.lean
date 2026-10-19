import Mathlib.GroupTheory.IsPerfect
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Data.Complex.Basic

/-!
The representation argument turning an invariant nondegenerate eigenspace
into a fixed vector. Perfectness of the acting group is explicit. The
concrete lifted SU(2) action and its perfectness are not constructed here.
-/

noncomputable section
namespace MagHK.Symmetry

variable {G H : Type*} [Group G] [AddCommGroup H] [Module ℂ H]

def lineCharacter (ρ : G →* Module.End ℂ H) (ψ : H) (hψ : ψ ≠ 0)
    (hline : ∀ g, ∃ c : ℂ, ρ g ψ = c • ψ) : G →* ℂ where
  toFun g := Classical.choose (hline g)
  map_one' := by
    apply smul_left_injective ℂ hψ
    calc
      _ = ρ 1 ψ := (Classical.choose_spec (hline 1)).symm
      _ = (1 : ℂ) • ψ := by simp
  map_mul' g h := by
    apply smul_left_injective ℂ hψ
    calc
      _ = ρ (g * h) ψ := (Classical.choose_spec (hline (g * h))).symm
      _ = ρ g (ρ h ψ) := by rw [map_mul]; rfl
      _ = ρ g (Classical.choose (hline h) • ψ) :=
        congrArg (ρ g) (Classical.choose_spec (hline h))
      _ = Classical.choose (hline h) • ρ g ψ := (ρ g).map_smul _ _
      _ = Classical.choose (hline h) • (Classical.choose (hline g) • ψ) := by
        exact congrArg (fun v => Classical.choose (hline h) • v)
          (Classical.choose_spec (hline g))
      _ = (Classical.choose (hline g) * Classical.choose (hline h)) • ψ := by
        rw [smul_smul, mul_comm]

theorem lineCharacter_action (ρ : G →* Module.End ℂ H) (ψ : H) (hψ : ψ ≠ 0)
    (hline : ∀ g, ∃ c : ℂ, ρ g ψ = c • ψ) (g : G) :
    ρ g ψ = lineCharacter ρ ψ hψ hline g • ψ :=
  Classical.choose_spec (hline g)

theorem perfect_character_trivial [Group.IsPerfect G] (χ : G →* ℂ) (g : G) : χ g = 1 := by
  let χu := χ.toHomUnits
  let : Group.IsPerfect χu.range := Group.IsPerfect.range χu
  have hr : (⟨χu g, ⟨g, rfl⟩⟩ : χu.range) = 1 := Subsingleton.elim _ _
  have hu : χu g = 1 := congrArg Subtype.val hr
  exact congrArg (fun u : ℂˣ => (u : ℂ)) hu

/-- An invariant complex line for a perfect group is pointwise fixed. -/
theorem invariant_line_fixed [Group.IsPerfect G]
    (ρ : G →* Module.End ℂ H) (ψ : H) (hψ : ψ ≠ 0)
    (hline : ∀ g, ∃ c : ℂ, ρ g ψ = c • ψ) : ∀ g, ρ g ψ = ψ := by
  intro g
  rw [lineCharacter_action ρ ψ hψ hline g,
    perfect_character_trivial (lineCharacter ρ ψ hψ hline) g, one_smul]

/-- The predicate may be membership in the ground eigenspace. Covariance
and one-dimensionality imply the fixed-vector conclusion. -/
theorem nondegenerate_invariant_subspace_fixed [Group.IsPerfect G]
    (ρ : G →* Module.End ℂ H) (P : H → Prop) (ψ : H) (hψ : ψ ≠ 0)
    (hground : P ψ) (hcovariant : ∀ g φ, P φ → P (ρ g φ))
    (hunique : ∀ φ, P φ → ∃ c : ℂ, φ = c • ψ) : ∀ g, ρ g ψ = ψ :=
  invariant_line_fixed ρ ψ hψ (fun g => hunique (ρ g ψ) (hcovariant g ψ hground))

end MagHK.Symmetry
