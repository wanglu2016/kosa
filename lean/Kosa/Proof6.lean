import Kosa.Module6

/-!
# 模組六的證明：阿那含必然成就初靜慮

論域是補特伽羅。`W.«果位» p = .«不還»` 讀作「p 是不還（阿那含）」，
`W.«成就淨初靜慮» p` 讀作「p 成就淨初靜慮」。

注意：目標所依的假定中，乙假十二（先離欲染、依未至入見道而證不還者成就無漏初靜慮）
狀態是「待核」。Lean 證明的是「若這些假定成立，則目標成立」；假定本身的真假，Lean 不管。
-/

namespace Kosa.M6

/-- 不還是聖者（不是異生）。 -/
theorem «不還是聖者» (W : «世界») (p : W.E) (h : W.«果位» p = .«不還») : «聖者» W p := by
  intro hYi
  rw [h] at hYi
  cases hYi

/-- 【定乙一】生在欲界或初靜慮的不還，成就淨初靜慮。依：乙假一、乙假五、乙假六。 -/
theorem «定乙一成立» (W : «世界») (a1 : «乙假一» W) (a5 : «乙假五» W) (a6 : «乙假六» W) :
    «定乙一» W := by
  intro p ⟨hBu, hNot⟩
  cases h : W.«生地» p
  case «生欲界» => exact a5 p ⟨h, a1 p hBu⟩      -- 生欲界：此生離欲染而得（乙假五）
  case «生初靜慮» => exact a6 p h               -- 生初靜慮（乙假六）
  all_goals                                    -- 其餘各地都是二定以上，與前提相違
    exfalso
    apply hNot
    simp [«生二定以上», «生無色界», h]

/-- 【定乙二】生在第二靜慮以上的不還，成就無漏初靜慮。
    依：乙假四、乙假十一、乙假十二、乙假十三、約乙三。 -/
theorem «定乙二成立» (W : «世界») (O : «本體公理» W)
    (a4 : «乙假四» W) (a11 : «乙假十一» W) (a12 : «乙假十二» W) (a13 : «乙假十三» W)
    (k3 : «約乙三» W) : «定乙二» W := by
  intro p ⟨hBu, hUp⟩
  rcases a4 p hUp with hYi | hSheng            -- 已離初靜慮染（乙假四）：作異生時，或作聖者時
  · -- 作異生時已離初靜慮染：看入見道依何地
    have hYu : «已離欲染» W p := by            -- 有初靜慮染之分，必已離欲染（本體）
      cases hw : W.«欲染» p
      case «未離欲染» =>
        have h := (O.«適用_初靜慮染» p).2 (by simp [«已離欲染», hw])
        rw [hYi] at h
        cases h
      case «異生離欲染» => exact Or.inl hw
      case «聖者離欲染» => exact Or.inr hw
    cases hd : W.«見道依地» p
    case «依未至» =>
      rcases hYu with hYY | hSY
      · exact a12 p ⟨hBu, hd, hYY⟩             -- 先離欲染、依未至（乙假十二，待核）
      · exact absurd hYi (k3 p hSY)            -- 作聖者時才離欲染，不可能先已離初靜慮染（約乙三）
    case «依初靜慮» => exact a13 p (Or.inl hd)
    case «依靜慮中間» => exact a13 p (Or.inr (Or.inl hd))
    case «依第二靜慮» => exact a13 p (Or.inr (Or.inr (Or.inl hd)))
    case «依第三靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inl hd))))
    case «依第四靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inr hd))))
    case «—» =>                                 -- 聖者必有見道依地
      exact absurd ((O.«適用_見道依地» p).1 hd) (by simp [«不還是聖者» W p hBu])
  · exact a11 p hSheng                          -- 作聖者時離初靜慮染（乙假十一）

/-- 【定乙三】生在第二靜慮以上的異生，不成就初靜慮。依：乙假四、乙假七、乙假八、乙假十、約乙一。 -/
theorem «定乙三成立» (W : «世界») (a4 : «乙假四» W) (a7 : «乙假七» W) (a8 : «乙假八» W)
    (a10 : «乙假十» W) (k1 : «約乙一» W) : «定乙三» W := by
  intro p ⟨hYi, hUp⟩ hCheng
  rcases (k1 p).1 hCheng with h | h | h
  · exact a8 p (a4 p hUp) h                    -- 味：已離初靜慮染，不成就（乙假八）
  · exact a7 p hUp h                           -- 淨：易地而捨（乙假七）
  · exact a10 p hYi h                          -- 無漏：異生不成就（乙假十）

/-- 【定乙四】預流、一來（及其向）不生上二界。依：乙假二、乙假三。 -/
theorem «定乙四成立» (W : «世界») (a2 : «乙假二» W) (a3 : «乙假三» W) : «定乙四» W :=
  fun p hPre hUp => a2 p hPre (a3 p hUp)

/-- 【定乙五】不還都成就無漏初靜慮（若乙假十二成立）。依：乙假一、乙假十二、乙假十三、乙假十四。 -/
theorem «定乙五成立» (W : «世界») (O : «本體公理» W)
    (a1 : «乙假一» W) (a12 : «乙假十二» W) (a13 : «乙假十三» W) (a14 : «乙假十四» W) :
    «定乙五» W := by
  intro p hBu
  rcases a1 p hBu with hYY | hSY
  · cases hd : W.«見道依地» p
    case «依未至» => exact a12 p ⟨hBu, hd, hYY⟩
    case «依初靜慮» => exact a13 p (Or.inl hd)
    case «依靜慮中間» => exact a13 p (Or.inr (Or.inl hd))
    case «依第二靜慮» => exact a13 p (Or.inr (Or.inr (Or.inl hd)))
    case «依第三靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inl hd))))
    case «依第四靜慮» => exact a13 p (Or.inr (Or.inr (Or.inr (Or.inr hd))))
    case «—» => exact absurd ((O.«適用_見道依地» p).1 hd) (by simp [«不還是聖者» W p hBu])
  · exact a14 p hSY

/-- 【目標乙】阿那含必然成就初靜慮。依：定乙一、定乙二、約乙一。 -/
theorem «目標乙成立» (W : «世界») (d1 : «定乙一» W) (d2 : «定乙二» W) (k1 : «約乙一» W) :
    «目標乙» W := by
  intro p hBu
  apply (k1 p).2
  cases h : W.«生地» p                         -- 就他生在哪一地分情況
  case «生欲界» =>                              -- 生欲界、初靜慮：淨（定乙一）
    exact Or.inr (Or.inl (d1 p ⟨hBu, by simp [«生二定以上», «生無色界», h]⟩))
  case «生初靜慮» =>
    exact Or.inr (Or.inl (d1 p ⟨hBu, by simp [«生二定以上», «生無色界», h]⟩))
  all_goals                                     -- 生二定以上：無漏（定乙二）
    exact Or.inr (Or.inr (d2 p ⟨hBu, by simp [«生二定以上», «生無色界», h]⟩))

/-- 把主證明拼起來：從九條假定、約定直接到目標。 -/
theorem «目標乙由諸假定» (W : «世界») (O : «本體公理» W) (k1 : «約乙一» W) (k3 : «約乙三» W)
    (a1 : «乙假一» W) (a4 : «乙假四» W) (a5 : «乙假五» W) (a6 : «乙假六» W)
    (a11 : «乙假十一» W) (a12 : «乙假十二» W) (a13 : «乙假十三» W) : «目標乙» W :=
  «目標乙成立» W («定乙一成立» W a1 a5 a6) («定乙二成立» W O a4 a11 a12 a13 k3) k1

/-- 另一條證明：經由定乙五，不分生地。 -/
theorem «目標乙_經無漏» (W : «世界») (O : «本體公理» W) (k1 : «約乙一» W)
    (a1 : «乙假一» W) (a12 : «乙假十二» W) (a13 : «乙假十三» W) (a14 : «乙假十四» W) :
    «目標乙» W :=
  fun p hBu => (k1 p).2 (Or.inr (Or.inr («定乙五成立» W O a1 a12 a13 a14 p hBu)))

end Kosa.M6
