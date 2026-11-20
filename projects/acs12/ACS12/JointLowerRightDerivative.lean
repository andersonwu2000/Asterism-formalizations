import ACS12.JointLowerRightSum

/-! The exact third response along the moving lower diagonal. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def lowerDiagonalMass (δ : ℝ) : ℝ := 1 - 2 * δ

noncomputable def lowerDiagonalRatio (δ : ℝ) : ℝ := (1 - δ) / lowerDiagonalMass δ

theorem lowerDiagonalRatio_mem {δ : ℝ} (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    lowerDiagonalRatio δ ∈ Icc 1 (7 / 6) := by
  have hM : 0 < lowerDiagonalMass δ := by unfold lowerDiagonalMass; linarith only [hD]
  exact ⟨(le_div_iff₀ hM).mpr (by unfold lowerDiagonalMass; linarith only [hδ]),
    (div_le_iff₀ hM).mpr (by unfold lowerDiagonalMass; linarith only [hD])⟩

noncomputable def lowerDiagonalRight (p δ : ℝ) : ℝ :=
  lowerDiagonalMass δ ^ (1 - p) * rightSourceSum 0 p (lowerDiagonalRatio δ)

noncomputable def lowerDiagonalRightD1 (p δ : ℝ) : ℝ :=
  let m := lowerDiagonalMass δ
  let U := lowerDiagonalRatio δ
  2 * (p - 1) * (m ^ (-p) * rightSourceSum 0 p U) + m ^ (-p - 1) * rightSourceSum 1 p U

noncomputable def lowerDiagonalRightD2 (p δ : ℝ) : ℝ :=
  let m := lowerDiagonalMass δ
  let U := lowerDiagonalRatio δ
  4 * p * (p - 1) * (m ^ (-p - 1) * rightSourceSum 0 p U) +
    4 * p * (m ^ (-p - 2) * rightSourceSum 1 p U) +
    m ^ (-p - 3) * rightSourceSum 2 p U

private theorem lowerDiagonalRight_atom_deriv {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ)
    (hD : δ ≤ 1 / 8) (r : ℝ) {k : ℕ} (hk : k < 4) :
    let m := lowerDiagonalMass δ
    let U := lowerDiagonalRatio δ
    HasDerivAt (fun d => lowerDiagonalMass d ^ r * rightSourceSum k p (lowerDiagonalRatio d))
      ((-2 * r) * (m ^ (r - 1) * rightSourceSum k p U) + m ^ (r - 2) * rightSourceSum (k + 1) p U) δ := by
  dsimp only
  let m := lowerDiagonalMass δ
  let U := lowerDiagonalRatio δ
  have hM : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hUR := lowerDiagonalRatio_mem hδ hD
  have hU : U ∈ Ioo 0 2 := ⟨zero_lt_one.trans_le hUR.1,hUR.2.trans_lt (by norm_num)⟩
  have hDm : HasDerivAt lowerDiagonalMass (-2) δ := by
    simpa only [lowerDiagonalMass,id_eq,mul_one] using ((hasDerivAt_id δ).const_mul 2).const_sub 1
  have hDu : HasDerivAt lowerDiagonalRatio (1 / m ^ 2) δ := by
    have h := ((hasDerivAt_id δ).const_sub 1).div hDm hM.ne'
    convert h using 1
    change 1 / m ^ 2 = ((-1 : ℝ) * m - (1 - δ) * (-2)) / m ^ 2
    unfold m lowerDiagonalMass
    ring
  have hF := (rightSourceSum_hasDerivAt hp hP hU hk).comp δ hDu
  have hR := hDm.rpow_const (p := r) (Or.inl hM.ne')
  convert hR.mul hF using 1
  simp only [Function.comp_apply]
  change (-2 * r) * (m ^ (r - 1) * rightSourceSum k p U) +
    m ^ (r - 2) * rightSourceSum (k + 1) p U =
    (-2 * r) * m ^ (r - 1) * rightSourceSum k p U +
    m ^ r * (rightSourceSum (k + 1) p U * (1 / m ^ 2))
  rw [Real.rpow_sub hM r 2,Real.rpow_two]
  ring

theorem lowerDiagonalRight_deriv1 {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerDiagonalRight p) (lowerDiagonalRightD1 p δ) δ := by
  convert lowerDiagonalRight_atom_deriv hp hP hδ hD (1 - p) (k := 0) (by decide) using 1
  simp only [lowerDiagonalRightD1,show 1 - p - 1 = -p by ring,show 1 - p - 2 = -p - 1 by ring]
  ring

theorem lowerDiagonalRight_deriv2 {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerDiagonalRightD1 p) (lowerDiagonalRightD2 p δ) δ := by
  have h₀ := (lowerDiagonalRight_atom_deriv hp hP hδ hD (-p) (k := 0) (by decide)).const_mul (2 * (p - 1))
  have h₁ := lowerDiagonalRight_atom_deriv hp hP hδ hD (-p - 1) (k := 1) (by decide)
  convert h₀.add h₁ using 1
  simp only [lowerDiagonalRightD2,show -p - 1 - 1 = -p - 2 by ring,show -p - 1 - 2 = -p - 3 by ring]
  ring

theorem lowerDiagonalRight_deriv3 {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerDiagonalRightD2 p)
      (p * (p + 1) * lowerDiagonalMass δ ^ (-p - 2) *
        lowerRightResponseTotal p (lowerDiagonalRatio δ)) δ := by
  let m := lowerDiagonalMass δ
  let U := lowerDiagonalRatio δ
  have hp₀ := zero_lt_one.trans_le hp
  have hM : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hUR := lowerDiagonalRatio_mem hδ hD
  have hU : U ∈ Ioo 0 2 := ⟨zero_lt_one.trans_le hUR.1,hUR.2.trans_lt (by norm_num)⟩
  have hEll : 2 * U - 1 = m⁻¹ := by
    unfold U lowerDiagonalRatio
    change 2 * ((1 - δ) / m) - 1 = m⁻¹
    field_simp [hM.ne']
    unfold m lowerDiagonalMass
    ring
  have h₀ := (lowerDiagonalRight_atom_deriv hp hP hδ hD (-p - 1) (k := 0) (by decide)).const_mul (4 * p * (p - 1))
  have h₁ := (lowerDiagonalRight_atom_deriv hp hP hδ hD (-p - 2) (k := 1) (by decide)).const_mul (4 * p)
  have h₂ := lowerDiagonalRight_atom_deriv hp hP hδ hD (-p - 3) (k := 2) (by decide)
  convert (h₀.add h₁).add h₂ using 1
  change p * (p + 1) * m ^ (-p - 2) * lowerRightResponseTotal p U = _
  rw [lowerRightResponseTotal_eq hp hP hU,hEll]
  change _ = 4 * p * (p - 1) *
      ((-2 * (-p - 1)) * (m ^ (-p - 1 - 1) * rightSourceSum 0 p U) +
        m ^ (-p - 1 - 2) * rightSourceSum 1 p U) +
    4 * p *
      ((-2 * (-p - 2)) * (m ^ (-p - 2 - 1) * rightSourceSum 1 p U) +
        m ^ (-p - 2 - 2) * rightSourceSum 2 p U) +
    ((-2 * (-p - 3)) * (m ^ (-p - 3 - 1) * rightSourceSum 2 p U) +
        m ^ (-p - 3 - 2) * rightSourceSum 3 p U)
  have hR (k : ℕ) : m ^ (-p - 2 - (k : ℝ)) = m ^ (-p - 2) / m ^ k := by
    rw [Real.rpow_sub hM,Real.rpow_natCast]
  have h₁' := hR 1
  have h₂' := hR 2
  have h₃' := hR 3
  norm_num at h₁' h₂' h₃'
  rw [show -p - 1 - 1 = -p - 2 by ring,show -p - 1 - 2 = -p - 2 - 1 by ring,h₁',
    show -p - 2 - 2 = -p - 2 - (2 : ℝ) by rfl,h₂',
    show -p - 3 - 1 = -p - 2 - 2 by ring,h₂',show -p - 3 - 2 = -p - 2 - 3 by ring,h₃']
  field_simp [hp₀.ne',hM.ne',show p + 1 ≠ 0 by positivity]
  ring

end ACS12.GammaMeasure
