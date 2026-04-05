/-
  Local Resonance in Block-Compressed Collatz Dynamics
  Lean 4 formal verification of the "Proved" components

  Reference: Kojiya, S. (April 2026)
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! ## Section 2: Block-compressed odd-to-odd dynamics -/

/-- A block affine map on ℚ: F_a(m) = slope * m + intercept -/
@[ext]
structure BlockMap where
  slope : ℚ
  intercept : ℚ
  deriving Repr, DecidableEq

namespace BlockMap

def eval (f : BlockMap) (m : ℚ) : ℚ := f.slope * m + f.intercept

def comp (g f : BlockMap) : BlockMap where
  slope := g.slope * f.slope
  intercept := g.slope * f.intercept + g.intercept

/-- Proposition 2.1: Composition of block-affine maps distributes over evaluation -/
theorem comp_eval (g f : BlockMap) (m : ℚ) :
    (comp g f).eval m = g.eval (f.eval m) := by
  simp [eval, comp]
  ring

/-- The slope of a composition is the product of slopes -/
theorem comp_slope (g f : BlockMap) : (comp g f).slope = g.slope * f.slope := rfl

/-- Composition is associative -/
theorem comp_assoc (h g f : BlockMap) : comp h (comp g f) = comp (comp h g) f := by
  ext <;> simp [comp] <;> ring

/-- Identity block map -/
def idMap : BlockMap := ⟨1, 0⟩

theorem idMap_eval (m : ℚ) : idMap.eval m = m := by simp [eval, idMap]

theorem idMap_comp (f : BlockMap) : comp idMap f = f := by
  ext <;> simp [comp, idMap]

theorem comp_idMap (f : BlockMap) : comp f idMap = f := by
  ext <;> simp [comp, idMap] <;> ring

end BlockMap

/-! ## Corollary 2.2: Closure equation for a periodic word -/

/-- If f.eval m = m and f.slope ≠ 1, then m = f.intercept / (1 - f.slope) -/
theorem fixed_point_formula (f : BlockMap) (m : ℚ) (hfix : f.eval m = m)
    (hne : f.slope ≠ 1) : m = f.intercept / (1 - f.slope) := by
  have h : f.slope * m + f.intercept = m := hfix
  have h1 : f.intercept = m * (1 - f.slope) := by linarith
  have h2 : 1 - f.slope ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  field_simp at h1 ⊢
  linarith

/-- The fixed point is unique -/
theorem fixed_point_unique (f : BlockMap) (m₁ m₂ : ℚ)
    (h1 : f.eval m₁ = m₁) (h2 : f.eval m₂ = m₂) (hne : f.slope ≠ 1) :
    m₁ = m₂ := by
  have := fixed_point_formula f m₁ h1 hne
  have := fixed_point_formula f m₂ h2 hne
  linarith

/-! ## Proposition 2.3: Local resonance reduction -/

/-- If f(ξ) = g(ξ) and f.slope ≠ g.slope, then ξ is uniquely determined -/
theorem local_resonance_reduction (f g : BlockMap) (ξ : ℚ)
    (hcoinc : f.eval ξ = g.eval ξ) (hne : f.slope ≠ g.slope) :
    ξ = (g.intercept - f.intercept) / (f.slope - g.slope) := by
  simp [BlockMap.eval] at hcoinc
  have hd : f.slope - g.slope ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  linarith

/-- Required height is unique -/
theorem required_height_unique (f g : BlockMap) (ξ₁ ξ₂ : ℚ)
    (h1 : f.eval ξ₁ = g.eval ξ₁) (h2 : f.eval ξ₂ = g.eval ξ₂)
    (hne : f.slope ≠ g.slope) : ξ₁ = ξ₂ := by
  have := local_resonance_reduction f g ξ₁ h1 hne
  have := local_resonance_reduction f g ξ₂ h2 hne
  linarith

/-! ## Lemma 4.1: Raw same-stage counting (core bound) -/

/-- Any two integers in an open interval of radius L differ by less than 2L -/
theorem integers_in_interval_bound (c L : ℚ) (t₁ t₂ : ℤ)
    (h1l : c - L < ↑t₁) (h1r : (↑t₁ : ℚ) < c + L)
    (h2l : c - L < ↑t₂) (h2r : (↑t₂ : ℚ) < c + L) :
    |(↑(t₁ - t₂) : ℚ)| < 2 * L := by
  push_cast
  rw [abs_lt]
  constructor <;> linarith
