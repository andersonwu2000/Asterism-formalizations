import Mathlib.Tactic

/-! A single positive Bernstein polynomial pays the full-SELF elasticity at every real anchor above one. -/
namespace ACS12.NativeCells
set_option maxHeartbeats 1600000
noncomputable def anchorElasticityDen (β x : ℝ):=x*(18-8*β)+50*(1+β)
noncomputable def anchorSelfDen (β x : ℝ):=8+β*(x+2)

theorem compensatedElasticity_numerator_pos {β x m δ : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (hx : 0<x)
    (hm : 9*x/anchorElasticityDen β x≤m)
    (hδ : (5*β+6)/(x*anchorSelfDen β x)≤δ) :
    0<β*(2*m-1)+(2+β)*δ := by
  let D:=anchorElasticityDen β x
  let H:=anchorSelfDen β x
  let K₂:=((14*x-153)^2+55691)/28
  let K₃:=((4*x-25)^2+35)/4
  let P:=β*x*H*(18*x-D)+(2+β)*(5*β+6)*D
  have hβc : 0≤1-β:=sub_nonneg.mpr hβ₁
  have hx₀ : 0<x:=hx
  have hD : 0<D := by
    have h : 0<18-8*β:=by linarith only [hβ₁]
    unfold D anchorElasticityDen
    positivity
  have hH : 0<H := by unfold H anchorSelfDen;positivity
  have hK₂ : 0<K₂ := by unfold K₂;positivity
  have hK₃ : 0<K₃ := by unfold K₃;positivity
  have hExpand : P/2=12*(9*x+25)*(1-β)^3+20*(11*x+80)*β*(1-β)^2+
      K₂*β^2*(1-β)+(x+10)*K₃*β^3 := by
    unfold P D H K₂ K₃ anchorElasticityDen anchorSelfDen
    ring
  have hP : 0<P := by
    by_cases hz : β=0
    · rw [hz] at hExpand
      norm_num at hExpand
      linarith only [hExpand,hx]
    · have hβ₀ : 0<β:=lt_of_le_of_ne hβ (Ne.symm hz)
      have hPos : 0<12*(9*x+25)*(1-β)^3+20*(11*x+80)*β*(1-β)^2+
          K₂*β^2*(1-β)+(x+10)*K₃*β^3 := by positivity
      linarith only [hExpand,hPos]
  have hE : β*(2*(9*x/D)-1)+(2+β)*((5*β+6)/(x*H))=P/(D*x*H) := by
    unfold P
    field_simp [hD.ne',hx₀.ne',hH.ne']
    <;>ring
  have hBase : 0<β*(2*(9*x/D)-1)+(2+β)*((5*β+6)/(x*H)) := by
    rw [hE]
    exact div_pos hP (mul_pos (mul_pos hD hx₀) hH)
  change 9*x/D≤m at hm
  change (5*β+6)/(x*H)≤δ at hδ
  have hM:=mul_le_mul_of_nonneg_left hm (show 0≤2*β by positivity)
  have hS:=mul_le_mul_of_nonneg_left hδ (show 0≤2+β by positivity)
  linarith only [hBase,hM,hS]

theorem compensatedElasticity_lower {β x m δ : ℝ}
    (hβ : 0≤β) (hβ₁ : β≤1) (hx : 0<x) (hδ₁ : δ<1)
    (hm : 9*x/anchorElasticityDen β x≤m)
    (hδ : (5*β+6)/(x*anchorSelfDen β x)≤δ) :
    2+β<(2+2*β*m)/(1-δ) := by
  have h:=compensatedElasticity_numerator_pos hβ hβ₁ hx hm hδ
  apply (lt_div_iff₀ (sub_pos.mpr hδ₁)).mpr
  nlinarith only [h]

end ACS12.NativeCells
