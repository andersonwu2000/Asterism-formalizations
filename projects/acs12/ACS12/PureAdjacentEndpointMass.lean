import ACS12.AdjacentCapMass
import ACS12.PureNativeBasics

/-! The frozen endpoint sampling mass and positions. -/
namespace ACS12.GammaMeasure

noncomputable def upperCapMass (u : ℝ) : ℝ :=
  u * (5 / 7 + (2304 / 8575) * u ^ 2)

theorem upperCapMass_eq (u : ℝ) : upperCapMass u = adjacentCap (9 / 5) u := by
  simp [upperCapMass, adjacentCap]

noncomputable def upperAtomX (j u : ℝ) : ℝ := u + j * upperCapMass u

noncomputable def upperSignedAtom (j u : ℝ) : ℝ := upperCapMass u * pureRight (9 / 5) u (upperAtomX j u)

theorem upperCapMass_pos {u : ℝ} (hu : 0 < u) : 0 < upperCapMass u := by unfold upperCapMass; positivity

theorem upperAtomX_pos {j u : ℝ} (hj : 0 ≤ j) (hu : 0 < u) : 0 < upperAtomX j u :=
  add_pos_of_pos_of_nonneg hu (mul_nonneg hj (upperCapMass_pos hu).le)

end ACS12.GammaMeasure
