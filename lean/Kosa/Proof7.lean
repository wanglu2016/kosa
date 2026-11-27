import Kosa.Proof4

/-!
# 三道題的證明（2026-11）

一、五識俱思是意業嗎？——是（業品26），且確有五識俱思（業品27）。
二、哪些蘊處界中沒有任何律儀？——受、想、識三蘊（業品31），十一處（業品32），
    十七界（業品33）；色、行二蘊與法處、法界有律儀（業品34）。
三、幾地有樂受？——三地：欲界、初靜慮、第三靜慮（根品27、根品28）。
    生幾地容成就樂根？——九地都容有（賢聖品12）。

讀法見 Proof4.lean 開頭的說明。每條「«編號成立»」的前提，恰是命題庫中這條的「依」；
`O : «本體公理» W` 是本體的適用條件（某門只對某類法有值），不算在「依」裡。
-/

namespace Kosa.Lib

/-! ## 小引理：某門有值，則是某類法（來自本體的適用條件） -/

/-- 有色自性者是色。 -/
theorem «有色自性則是色» (W : «世界») (O : «本體公理» W) (x : W.«法»)
    (h : W.«色自性» x ≠ .«—») : W.«法類» x = .«色» := by
  by_cases hx : W.«法類» x = .«色»
  · exact hx
  · exact absurd ((O.«適用_色自性» x).2 hx) h

/-- 有心所自性者是心所。 -/
theorem «有心所自性則是心所» (W : «世界») (O : «本體公理» W) (x : W.«法»)
    (h : W.«心所自性» x ≠ .«—») : W.«法類» x = .«心所» := by
  by_cases hx : W.«法類» x = .«心所»
  · exact hx
  · exact absurd ((O.«適用_心所自性» x).2 hx) h

/-- 屬六識之一者是心。 -/
theorem «有六識則是心» (W : «世界») (O : «本體公理» W) (x : W.«法»)
    (h : W.«六識» x ≠ .«—») : W.«法類» x = .«心» := by
  by_cases hx : W.«法類» x = .«心»
  · exact hx
  · exact absurd ((O.«適用_六識» x).2 hx) h

/-! ## 律儀之體 -/

/-- 律儀（無表三種中的律儀）唯是無表色，故是色。頌：「無表三律儀，不律儀非二」。 -/
theorem «無表律儀是無表色» (W : «世界») (O : «本體公理» W) (x : W.«法»)
    (h : W.«律儀種» x = .«律儀») : W.«色自性» x = .«無表色» ∧ W.«法類» x = .«色» := by
  have hz : W.«色自性» x = .«無表色» := by
    by_cases hz : W.«色自性» x = .«無表色»
    · exact hz
    · have h' := (O.«適用_律儀種» x).2 hz   -- 若非無表色，則無律儀種
      rw [h] at h'                           -- 但它是律儀
      cases h'                               -- 相違
  exact ⟨hz, «有色自性則是色» W O x (by rw [hz]; decide)⟩

/-- 意根律儀唯是慧、念，故是心所。頌：「正知正念合，名意根律儀」。 -/
theorem «意根律儀是慧念» (W : «世界») (O : «本體公理» W) (x : W.«法»)
    (h : W.«根律儀» x = .«意根律儀») :
    (W.«心所自性» x = .«慧» ∨ W.«心所自性» x = .«念») ∧ W.«法類» x = .«心所» := by
  have hz : W.«心所自性» x = .«慧» ∨ W.«心所自性» x = .«念» := by
    by_cases hz : W.«心所自性» x = .«慧» ∨ W.«心所自性» x = .«念»
    · exact hz
    · have h' := (O.«適用_根律儀» x).2 hz   -- 若非慧非念，則無根律儀
      rw [h] at h'                           -- 但它是意根律儀
      cases h'                               -- 相違
  refine ⟨hz, «有心所自性則是心所» W O x ?_⟩
  rcases hz with hz | hz <;> (rw [hz]; decide)

/-- 諸律儀之體：或是無表色（色，無心所自性，非識），或是慧、念（心所，無色自性，非識）。
    下面三條「非諸律儀」都由這一條推出。 -/
theorem «諸律儀之體» (W : «世界») (O : «本體公理» W) (x : W.«法») (h : «諸律儀» W x) :
    (W.«法類» x = .«色» ∧ W.«色自性» x = .«無表色» ∧ W.«心所自性» x = .«—» ∧ W.«六識» x = .«—») ∨
    (W.«法類» x = .«心所» ∧ W.«色自性» x = .«—» ∧ W.«心所自性» x = .«慧» ∧ W.«六識» x = .«—») ∨
    (W.«法類» x = .«心所» ∧ W.«色自性» x = .«—» ∧ W.«心所自性» x = .«念» ∧ W.«六識» x = .«—») := by
  rcases h with h | h
  · obtain ⟨hz, hc⟩ := «無表律儀是無表色» W O x h
    have h3 : W.«心所自性» x = .«—» := (O.«適用_心所自性» x).2 (by rw [hc]; decide)
    have h4 : W.«六識» x = .«—» := (O.«適用_六識» x).2 (by rw [hc]; decide)
    exact Or.inl ⟨hc, hz, h3, h4⟩
  · obtain ⟨hz, hc⟩ := «意根律儀是慧念» W O x h
    have h2 : W.«色自性» x = .«—» := (O.«適用_色自性» x).2 (by rw [hc]; decide)
    have h4 : W.«六識» x = .«—» := (O.«適用_六識» x).2 (by rw [hc]; decide)
    rcases hz with hz | hz
    · exact Or.inr (Or.inl ⟨hc, h2, hz, h4⟩)
    · exact Or.inr (Or.inr ⟨hc, h2, hz, h4⟩)

/-! ## 第一題：五識俱思是意業 -/

/-- 【業品26】五識俱思是意業：意業即思（頌「思即是意業」），與哪一識俱無關。 -/
theorem «業品26成立» (W : «世界») : «業品26» W := by
  intro x y h
  exact h.1

/-- 【業品27】確有五識俱思：有眼識（界品46），它是心；凡心必有思相應（根品24）；相應是對稱的。 -/
theorem «業品27成立» (W : «世界») (O : «本體公理» W) (a24 : «根品24» W) (a46 : «界品46» W) :
    «業品27» W := by
  obtain ⟨y, hy⟩ := a46.1                                   -- 有一眼識 y
  have hXin : W.«法類» y = .«心» := «有六識則是心» W O y (by rw [hy]; decide)
  obtain ⟨x, hx, hyx⟩ := a24 y hXin                          -- y 有思 x 相應
  exact ⟨x, y, hx, O.«對稱_相應» y x hyx, Or.inl hy⟩

/-! ## 第二題：哪些蘊處界中沒有任何律儀 -/

/-- 【業品31】受、想、識三蘊中沒有律儀。 -/
theorem «業品31成立» (W : «世界») (O : «本體公理» W) : «業品31» W := by
  intro x hx hl
  simp only [«受蘊», «想蘊», «識蘊»] at hx
  rcases «諸律儀之體» W O x hl with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
  rcases hx with h | h | h <;>
  first
    | (rw [h1] at h; cases h)
    | (rw [h2] at h; cases h)
    | (rw [h3] at h; cases h)
    | (rw [h4] at h; cases h)

/-- 【業品32】十一處（除法處）中沒有律儀。 -/
theorem «業品32成立» (W : «世界») (O : «本體公理» W) : «業品32» W := by
  intro x hx hl
  simp only [«眼處», «耳處», «鼻處», «舌處», «身處», «意處»] at hx
  rcases «諸律儀之體» W O x hl with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
  rcases hx with h | h | h | h | h | h | h | h | h | h | h <;>
  first
    | (rw [h1] at h; cases h)
    | (rw [h2] at h; cases h)
    | (rw [h3] at h; cases h)
    | (rw [h4] at h; cases h)

/-- 【業品33】十七界（除法界）中沒有律儀。 -/
theorem «業品33成立» (W : «世界») (O : «本體公理» W) : «業品33» W := by
  intro x hx hl
  simp only [«眼界», «耳界», «鼻界», «舌界», «身界», «意界», «聲界», «香界», «味界», «觸界»,
    «眼識界», «耳識界», «鼻識界», «舌識界», «身識界», «意識界»] at hx
  rcases «諸律儀之體» W O x hl with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  first
    | (rw [h1] at h; cases h)
    | (rw [h2] at h; cases h)
    | (rw [h3] at h; cases h)
    | (rw [h4] at h; cases h)

/-- 【業品34】色蘊、行蘊、法處、法界中有律儀：無表律儀（業品28）是色蘊、法處、法界；
    意根律儀（業品30）是慧、念，屬行蘊。 -/
theorem «業品34成立» (W : «世界») (O : «本體公理» W) (a28 : «業品28» W) (a30 : «業品30» W) :
    «業品34» W := by
  obtain ⟨x, hx⟩ := a28.1                                    -- 有律儀 x
  obtain ⟨y, hy⟩ := a30                                      -- 有意根律儀 y
  obtain ⟨zx, cx⟩ := «無表律儀是無表色» W O x hx
  obtain ⟨zy, cy⟩ := «意根律儀是慧念» W O y hy
  have fx : «法處» W x := Or.inr (Or.inr (Or.inr (Or.inl zx)))
  have xy : «行蘊» W y := by
    refine ⟨Or.inr cy, ?_, ?_⟩ <;> rcases zy with h | h <;> (rw [h]; decide)
  exact ⟨⟨x, cx, Or.inl hx⟩, ⟨y, xy, Or.inr hy⟩, ⟨x, fx, Or.inl hx⟩, ⟨x, fx, Or.inl hx⟩⟩

/-! ## 第三題（甲）：樂受唯在欲界、初靜慮、第三靜慮 -/

/-- 【根品27】樂受唯在欲界地、初靜慮地、第三靜慮地。
    樂受或在第三靜慮地，或與身識相應（根品25）。身識是五識之一，唯有伺（界品57）、
    唯有漏（界品58），故唯在欲界或初靜慮（Proof4 的小引理，用界品1、界品11）；
    相應的心、心所同地（根品3），故樂受亦在欲界或初靜慮。 -/
theorem «根品27成立» (W : «世界») (O : «本體公理» W) (a25 : «根品25» W) (a57 : «界品57» W)
    (a58 : «界品58» W) (a11 : «界品11» W) (k1 : «界品1» W) (a3 : «根品3» W) :
    «根品27» W := by
  intro x hx
  rcases a25 x hx with h3 | ⟨y, hy, hxy⟩
  · exact Or.inr (Or.inr h3)                                 -- 第三靜慮地
  · have hXin : W.«法類» y = .«心» := «有六識則是心» W O y (by rw [hy]; decide)
    have h5 : «五識» W y := Or.inr (Or.inr (Or.inr (Or.inr hy)))
    have hk : W.«繫不繫» x = W.«繫不繫» y := a3 x y hxy      -- 相應同地
    rcases «有伺有漏心唯欲界或初靜慮» W k1 a11 y hXin (a57 y h5) (a58 y h5) with h | h
    · exact Or.inl (hk.trans h)                              -- 欲界
    · exact Or.inr (Or.inl (Or.inl (hk.trans h)))            -- 初靜慮

/-- 無漏有為法才有「依地」；有依地者無漏，故不繫（界品1）。 -/
theorem «依地有值則不繫» (W : «世界») (O : «本體公理» W) (k1 : «界品1» W) (x : W.«法»)
    (h : W.«依地» x ≠ .«—») : W.«繫不繫» x = .«不繫» := by
  have hw : W.«有漏無漏» x = .«無漏» := by
    by_cases hw : W.«有漏無漏» x = .«無漏» ∧ «有為» W x
    · exact hw.1
    · exact absurd ((O.«適用_依地» x).2 hw) h
  exact (k1 x).1 hw

/-- 【根品28】其餘六地沒有樂受。九地各以「X繫或依X地之無漏」界定；
    樂受在欲界、初靜慮、第三靜慮（根品27），與其餘六地兩兩相違：
    同是繫地則地不同；一是繫地、一是無漏依地，則無漏者不繫，與有繫相違。 -/
theorem «根品28成立» (W : «世界») (O : «本體公理» W) (a27 : «根品27» W) (k1 : «界品1» W) :
    «根品28» W := by
  intro x hx hbad
  have hn := «依地有值則不繫» W O k1 x
  have hg := a27 x hx
  simp only [«欲界地», «初靜慮地», «第二靜慮地», «第三靜慮地», «第四靜慮地», «空無邊處地»,
    «識無邊處地», «無所有處地», «非想非非想處地»] at hg hbad
  rcases hg with h | (h | h | h | h) | (h | h) <;>
  rcases hbad with (g | g) | (g | g) | (g | g) | (g | g) | (g | g) | g <;>
  first
    | (rw [h] at g; cases g)
    | (have hb := hn (by rw [h]; decide); rw [hb] at g; cases g)
    | (have hb := hn (by rw [g]; decide); rw [hb] at h; cases h)

/-! ## 第三題（乙）：生九地皆容成就樂根 -/

/-- 【賢聖品12】生九地，各有成就樂根的有情。
    生欲界者必成就樂根（賢聖品7，頌「極少八無善，成受身命意」），且有生欲界者（賢聖品9）；
    聖者必成就樂根（賢聖品8，頌「二無漏十一，初無漏十三」：至少成就三無漏根，其中有樂根），
    上八地各有聖者（賢聖品10）。 -/
theorem «賢聖品12成立» (W : «世界») (a7 : «賢聖品7» W) (a8 : «賢聖品8» W) (a9 : «賢聖品9» W)
    (a10 : «賢聖品10» W) : «賢聖品12» W := by
  obtain ⟨p0, g0⟩ := a9
  obtain ⟨x0, l0, c0⟩ := a7 p0 g0
  obtain ⟨⟨p1, g1, s1⟩, ⟨p2, g2, s2⟩, ⟨p3, g3, s3⟩, ⟨p4, g4, s4⟩, ⟨p5, g5, s5⟩, ⟨p6, g6, s6⟩,
    ⟨p7, g7, s7⟩, ⟨p8, g8, s8⟩⟩ := a10
  obtain ⟨x1, l1, c1⟩ := a8 p1 s1
  obtain ⟨x2, l2, c2⟩ := a8 p2 s2
  obtain ⟨x3, l3, c3⟩ := a8 p3 s3
  obtain ⟨x4, l4, c4⟩ := a8 p4 s4
  obtain ⟨x5, l5, c5⟩ := a8 p5 s5
  obtain ⟨x6, l6, c6⟩ := a8 p6 s6
  obtain ⟨x7, l7, c7⟩ := a8 p7 s7
  obtain ⟨x8, l8, c8⟩ := a8 p8 s8
  exact ⟨⟨p0, x0, g0, l0, c0⟩, ⟨p1, x1, g1, l1, c1⟩, ⟨p2, x2, g2, l2, c2⟩, ⟨p3, x3, g3, l3, c3⟩,
    ⟨p4, x4, g4, l4, c4⟩, ⟨p5, x5, g5, l5, c5⟩, ⟨p6, x6, g6, l6, c6⟩, ⟨p7, x7, g7, l7, c7⟩,
    ⟨p8, x8, g8, l8, c8⟩⟩

end Kosa.Lib
