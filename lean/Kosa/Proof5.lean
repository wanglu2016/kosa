import Kosa.Module5

/-!
# 模組五的證明：阿羅漢最後心是苦諦、集諦

讀法與 Proof4.lean 相同：括號裡是前提，冒號後是結論，`by` 之後是證明步驟。
每條定理的前提，恰好是命題文件裡這條定理的「依」。

`W.«阿羅漢最後心» x` 讀作「x 是阿羅漢最後心」。
-/

namespace Kosa.M5

/-- 【定甲一】最後心不是道諦。依：甲假一（二無記涅槃）、甲假六（道諦唯善）。 -/
theorem «定甲一成立» (W : «世界») (a1 : «甲假一» W) (a6 : «甲假六» W) : «定甲一» W := by
  intro x hx hDao
  have h := a6 x hDao          -- 若是道諦，則是善（甲假六）
  rw [a1 x hx] at h            -- 但它是無覆無記（甲假一）
  cases h                      -- 相違

/-- 【定甲二】最後心是有漏。依：定甲一、約甲二。
    它是心，故是有為；無漏的有為就是道諦；它不是道諦，所以不是無漏。 -/
theorem «定甲二成立» (W : «世界») (d1 : «定甲一» W) (k2 : «約甲二» W) : «定甲二» W := by
  intro x hx
  cases h : W.«有漏無漏» x with
  | «有漏» => rfl
  | «無漏» =>
      exfalso
      apply d1 x hx              -- 只須說明它是道諦，便與定甲一相違
      refine ⟨h, ?_⟩            -- 它是無漏；還要說明它是有為
      intro hWu                  -- 設它是無為
      rw [k2 x hx] at hWu        -- 但它是心（約甲二）
      cases hWu

/-- 【目標甲】阿羅漢最後心是苦諦、集諦。依：定甲二。苦諦、集諦都定義為有漏。 -/
theorem «目標甲成立» (W : «世界») (d2 : «定甲二» W) : «目標甲» W :=
  fun x hx => ⟨d2 x hx, d2 x hx⟩

/-- 【定甲三】最後心是修所斷。依：定甲二、甲假七、甲假八、甲假一。 -/
theorem «定甲三成立» (W : «世界») (d2 : «定甲二» W) (a7 : «甲假七» W) (a8 : «甲假八» W)
    (a1 : «甲假一» W) : «定甲三» W := by
  intro x hx
  cases h : W.«斷非斷» x with
  | «修所斷» => rfl
  | «非所斷» =>                  -- 非所斷即無漏（甲假七），但它有漏（定甲二）
      have hWu := (a7 x).1 h
      rw [d2 x hx] at hWu
      cases hWu
  | «見所斷» =>                  -- 見所斷唯染（甲假八），但它無覆無記（甲假一）
      have hRan := a8 x h
      unfold «染» at hRan
      rw [a1 x hx] at hRan
      rcases hRan with h' | h' <;> cases h'

/-- 【定甲四】與最後心相應的心所，也是苦諦、集諦。依：甲假一、甲假九、甲假六。 -/
theorem «定甲四成立» (W : «世界») (O : «本體公理» W)
    (a1 : «甲假一» W) (a9 : «甲假九» W) (a6 : «甲假六» W) : «定甲四» W := by
  intro x y ⟨hx, hxy⟩
  have hyXing : W.«性» y = .«無覆無記» := by rw [← a9 x y hxy]; exact a1 x hx   -- 同性
  have hyXin := (O.«類型_相應» x y hxy).2.1                                   -- y 是心或心所
  have hLou : W.«有漏無漏» y = .«有漏» := by
    cases h : W.«有漏無漏» y with
    | «有漏» => rfl
    | «無漏» =>
        exfalso
        have hShan := a6 y ⟨h, by                 -- 若無漏，則是道諦（它是有為），故是善
          intro hWu
          rcases hyXin with h' | h' <;> (rw [h'] at hWu; cases hWu)⟩
        rw [hyXing] at hShan                       -- 但它無覆無記
        cases hShan
  exact ⟨hLou, hLou⟩

/-- 【定甲五】最後心是集諦，卻不是等無間緣。依：定甲二、甲假五。 -/
theorem «定甲五成立» (W : «世界») (d2 : «定甲二» W) (a5 : «甲假五» W) : «定甲五» W :=
  fun x hx => ⟨d2 x hx, a5 x hx⟩

/-- 【定甲六】最後心的全貌。依：甲假一、甲假二、甲假三、定甲二、定甲三。 -/
theorem «定甲六成立» (W : «世界») (a1 : «甲假一» W) (a2 : «甲假二» W) (a3 : «甲假三» W)
    (d2 : «定甲二» W) (d3 : «定甲三» W) : «定甲六» W :=
  fun x hx => ⟨a2 x hx, a3 x hx, a1 x hx, d2 x hx, d3 x hx⟩

/-- 【推論甲】若把「集」讀成「能生後心」（異讀甲），阿羅漢就沒有最後心。
    依：異讀甲、目標甲、甲假五、約甲二。 -/
theorem «推論甲成立» (W : «世界») (y1 : «異讀甲» W) (g : «目標甲» W) (a5 : «甲假五» W)
    (k2 : «約甲二» W) : «推論甲» W := by
  rintro ⟨x, hx⟩                                 -- 設有一個最後心 x
  exact a5 x hx (y1 x ⟨(g x hx).2, k2 x hx⟩)    -- 它是集諦之心，依異讀必是等無間緣——相違

/-! ## 從假定直接到目標 -/

/-- 目標只依三條：二無記涅槃（甲假一）、道諦唯善（甲假六）、最後心是心（約甲二）。 -/
theorem «目標甲由諸假定» (W : «世界») (k2 : «約甲二» W) (a1 : «甲假一» W) (a6 : «甲假六» W) :
    «目標甲» W :=
  «目標甲成立» W («定甲二成立» W («定甲一成立» W a1 a6) k2)

/-- 也可以不用約甲二：頌「最後意識滅」已說最後心是意識，意識是心。 -/
theorem «目標甲_以意識代心» (W : «世界») (O : «本體公理» W)
    (a1 : «甲假一» W) (a2 : «甲假二» W) (a6 : «甲假六» W) : «目標甲» W := by
  have k2 : «約甲二» W := by
    intro x hx
    have hYi := a2 x hx                            -- 它是意識
    by_cases h : W.«法類» x = .«心»
    · exact h
    · have := (O.«適用_六識» x).2 h                -- 不是心就沒有六識之分
      rw [hYi] at this
      cases this
  exact «目標甲由諸假定» W k2 a1 a6

end Kosa.M5
