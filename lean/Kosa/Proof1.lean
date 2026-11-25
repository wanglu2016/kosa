import Kosa.Module1

/-!
# 模組一的證明（由 Lean 內核檢查）

求解器在「至多 6 個法」的有界世界裡窮盡了反例；這裡的證明則對**任意大小**的世界成立。
所用前提就是引擎找出的極小前提集（16 條）。

證明分三段，與 2022 文的步驟大致對應：
* 引理「欲界有覆無記心唯內門轉」：對應 2022 文第 15–19、23–26 步；
* 定理「有覆無記色唯初靜慮繫」：對應第 27–48 步；
* 附：頌「欲無有覆表，以無等起故」作為定理；以及只用四條前提（兩條頌文）的短證明。
-/

namespace Kosa.M1

/-- 表色必是色：身表唯在色處、語表唯在聲處（值的適用條件），有色自性者必是色。 -/
theorem «表色是色» (W : «世界») (O : «本體公理» W) (x : W.E)
    (h : «表色» W x) : W.«法類» x = .«色» := by
  have hZi : W.«色自性» x ≠ .«—» := by
    rcases h with h | h
    · rw [O.«適用_身表» x h]; decide
    · rw [O.«適用_語表» x h]; decide
  by_cases hx : W.«法類» x = .«色»
  · exact hx
  · exact absurd ((O.«適用_色自性» x).2 hx) hZi

/-- 引理：欲界的有覆無記心唯內門轉。
    有覆無記心必有惑相應（補一），惑與心同性、同地（補二、補三）；
    欲界有覆無記惑唯身見、邊見及彼俱癡（前提9）；
    身見、邊見是見所斷（前提2），見所斷惑內門轉（前提1）；
    相應法同門轉（前提3乙），所以心也內門轉。 -/
theorem «欲界有覆無記心唯內門轉» (W : «世界»)
    (p1 : «前提1» W) (p2 : «前提2» W) (p3b : «前提3乙» W) (p9 : «前提9» W)
    (b1 : «補一» W) (b2 : «補二» W) (b3 : «補三» W)
    (c : W.E) (hcXin : W.«法類» c = .«心») (hcXing : W.«性» c = .«有覆無記»)
    (hk : W.«繫不繫» c = .«欲界繫») : W.«門轉» c = .«內門轉» := by
  -- 染心必有惑相應（補一）
  obtain ⟨y, hyHuo, hcy⟩ := b1 c ⟨hcXin, Or.inr hcXing⟩
  -- 惑與心同性、同地（補二、補三）
  have hyXing : W.«性» y = .«有覆無記» := by rw [← b2 c y hcy]; exact hcXing
  have hyXi : W.«繫不繫» y = .«欲界繫» := by rw [← b3 c y hcy]; exact hk
  -- 心的門轉與惑相同（前提3乙）
  rw [p3b c y hcy]
  -- 欲界有覆無記惑：身見、邊見，或與之相應的癡（前提9）
  rcases p9 y ⟨hyHuo, hyXi, hyXing⟩ with h | h | ⟨_, z, hyz, hz⟩
  · exact p1 y ⟨p2 y (Or.inl h), hyHuo⟩
  · exact p1 y ⟨p2 y (Or.inr (Or.inl h)), hyHuo⟩
  · -- 與癡相應的身見或邊見 z：五見，故是惑（定義）、見所斷（前提2）
    have hzWu : «五見» W z := by
      rcases hz with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    have hzHuo : «惑» W z := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hzWu))))
    rw [p3b y z hyz]
    exact p1 z ⟨p2 z hzWu, hzHuo⟩

/-- 有覆無記色是表色：它是業（前提10乙），而無表色是有記（前提15）。 -/
theorem «有覆無記色是表色» (W : «世界») (p10b : «前提10乙» W) (p15 : «前提15» W)
    (r : W.E) (hrXing : W.«性» r = .«有覆無記») (hrSe : W.«法類» r = .«色») :
    «表色» W r := by
  have hYe : «業» W r := p10b r ⟨hrSe, by rw [hrXing]; decide⟩
  rcases hYe with h | h
  · exact h
  · have hJi := p15 r h
    unfold «有記» at hJi
    rw [hrXing] at hJi
    rcases hJi with h' | h' <;> cases h'

/-- 2022 文的結論：有覆無記色唯初靜慮繫。
    前提恰為引擎找出的極小前提集。對任意世界成立。 -/
theorem «有覆無記色唯初靜慮繫» (W : «世界») (O : «本體公理» W)
    (p1 : «前提1» W) (p2 : «前提2» W) (p3b : «前提3乙» W) (p8 : «前提8» W)
    (p9 : «前提9» W) (p10a : «前提10甲» W) (p10b : «前提10乙» W)
    (p12 : «前提12» W) (p13 : «前提13» W) (p15 : «前提15» W)
    (b1 : «補一» W) (b2 : «補二» W) (b3 : «補三» W) (b4 : «補四» W)
    (b5 : «補五» W) (b6 : «補六» W) :
    «求證» W := by
  intro r hr
  obtain ⟨hrXing, hrSe⟩ := hr
  -- 是表色
  have hBiao := «有覆無記色是表色» W p10b p15 r hrXing hrSe
  -- 色由剎那等起成善染性（前提10甲）：有同性的等起心 c
  obtain ⟨c, hrc, hSame⟩ := p10a r ⟨hrSe, by rw [hrXing]; decide⟩
  have hcXing : W.«性» c = .«有覆無記» := by rw [← hSame]; exact hrXing
  have hcXin : W.«法類» c = .«心» := (O.«類型_剎那等起» r c hrc).2.1
  -- 能發表業的心外門轉（前提8），外門轉心有伺（前提12）
  have hcWai : W.«門轉» c = .«外門轉» := p8 r c ⟨hBiao, hrc⟩
  have hcSi : W.«有伺無伺» c = .«有伺» := p12 c ⟨hcWai, hcXin⟩
  -- 等起心有漏（補五），有漏即非不繫（補六）
  have hcLou : W.«有漏無漏» c = .«有漏» := b5 r c hrc
  have hNotBuxi : W.«繫不繫» c ≠ .«不繫» := by
    intro h
    have hWulou := (b6 c).2 h
    rw [hcLou] at hWulou
    cases hWulou
  -- 二定以上無伺（前提13）：c 不在二定以上
  have hNotUpper : ¬ «二定以上» W c := by
    intro h2
    have hWusi := p13 c ⟨h2, hcXin⟩
    rw [hcSi] at hWusi
    cases hWusi
  -- 欲界有覆無記心唯內門轉（引理），而 c 外門轉：c 不在欲界
  have hNotYu : W.«繫不繫» c ≠ .«欲界繫» := by
    intro hk
    have hNei := «欲界有覆無記心唯內門轉» W p1 p2 p3b p9 b1 b2 b3 c hcXin hcXing hk
    rw [hcWai] at hNei
    cases hNei
  -- 表業與等起心同地（補四）；剩下只有初靜慮
  rw [b4 r c hrc]
  cases hk : W.«繫不繫» c
  all_goals first
    | rfl
    | exact absurd hk hNotYu
    | exact absurd hk hNotBuxi
    | exact absurd (show «二定以上» W c by simp [«二定以上», «無色界繫», hk]) hNotUpper

/-- 頌「欲無有覆表，以無等起故」作為定理：
    欲界有覆無記表色的等起心，必是欲界有覆無記心（前提10甲、補四），
    它唯內門轉（引理），卻又必須外門轉（前提8）——所以沒有這樣的等起。 -/
theorem «欲無有覆表» (W : «世界») (O : «本體公理» W)
    (p1 : «前提1» W) (p2 : «前提2» W) (p3b : «前提3乙» W) (p8 : «前提8» W)
    (p9 : «前提9» W) (p10a : «前提10甲» W)
    (b1 : «補一» W) (b2 : «補二» W) (b3 : «補三» W) (b4 : «補四» W) :
    «頌三» W := by
  rintro ⟨r, hrYu, hrXing, hrBiao⟩
  have hrSe : W.«法類» r = .«色» := «表色是色» W O r hrBiao
  obtain ⟨c, hrc, hSame⟩ := p10a r ⟨hrSe, by rw [hrXing]; decide⟩
  have hcXing : W.«性» c = .«有覆無記» := by rw [← hSame]; exact hrXing
  have hcXin : W.«法類» c = .«心» := (O.«類型_剎那等起» r c hrc).2.1
  have hcWai : W.«門轉» c = .«外門轉» := p8 r c ⟨hrBiao, hrc⟩
  have hk : W.«繫不繫» c = .«欲界繫» := by rw [← b4 r c hrc]; exact hrYu
  have hNei := «欲界有覆無記心唯內門轉» W p1 p2 p3b p9 b1 b2 b3 c hcXin hcXing hk
  rw [hcWai] at hNei
  cases hNei

/-- 短證明：只用四條前提，其中兩條是頌文（「表唯有伺二」「欲無有覆表」）。
    掌握的前提越高層，證明越短。 -/
theorem «有覆無記色唯初靜慮繫_頌文版» (W : «世界»)
    (p10b : «前提10乙» W) (p15 : «前提15» W) (s2 : «頌二» W) (s3 : «頌三» W) :
    «求證» W := by
  intro r hr
  obtain ⟨hrXing, hrSe⟩ := hr
  have hBiao := «有覆無記色是表色» W p10b p15 r hrXing hrSe
  rcases s2 r hBiao with h | h
  · exact absurd ⟨r, h, hrXing, hBiao⟩ s3
  · exact h

/-- 轉讀法之衝突：若把前提8移到因等起上（異讀8），它與頌「見斷識唯轉」的肯定面（頌一乙）
    及 2022 文的前提1、3甲、3乙、6、補一合起來自相矛盾。對任意世界成立。 -/
theorem «轉讀法之衝突» (W : «世界») (O : «本體公理» W)
    (p1 : «前提1» W) (p3a : «前提3甲» W) (p3b : «前提3乙» W) (p6 : «前提6» W)
    (b1 : «補一» W) (s1b : «頌一乙» W) (a8 : «異讀8» W) : False := by
  -- 見所斷識能作表業的轉（頌一乙）
  obtain ⟨r, c, hrBiao, hrc, hcJian⟩ := s1b
  have hcXin : W.«法類» c = .«心» := (O.«類型_因等起» r c hrc).2.1
  -- 見所斷心是染（前提6：不染心非見所斷）
  have hcRan : «染» W c := by
    unfold «染»
    cases h : W.«性» c with
    | «不善» => exact Or.inl rfl
    | «有覆無記» => exact Or.inr rfl
    | «善» => exact absurd hcJian (p6 c ⟨Or.inl h, hcXin⟩)
    | «無覆無記» => exact absurd hcJian (p6 c ⟨Or.inr h, hcXin⟩)
  -- 染心有惑相應（補一），惑與心同所斷（前提3甲），見所斷惑內門轉（前提1）
  obtain ⟨y, hyHuo, hcy⟩ := b1 c ⟨hcXin, hcRan⟩
  have hyJian : W.«斷非斷» y = .«見所斷» := by rw [← p3a c y hcy]; exact hcJian
  have hyNei := p1 y ⟨hyJian, hyHuo⟩
  -- 作表業之轉的心外門轉（異讀8），相應法同門轉（前提3乙）
  have hcWai := a8 r c ⟨hrBiao, hrc⟩
  have hSame := p3b c y hcy
  rw [hcWai, hyNei] at hSame
  cases hSame

end Kosa.M1
