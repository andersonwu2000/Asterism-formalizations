import ACS12.QuarticTrial

/-! The logarithmic separation of two normalized physical mass cells. -/
namespace ACS12.NativeCells

noncomputable def quarticActualGap {n : ℕ} (w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  Real.log (Real.sin (halfArc (quarticCellAngle w) i j) /
    Real.sqrt (Real.sin (Real.pi * w i) * Real.sin (Real.pi * w j)))

end ACS12.NativeCells
