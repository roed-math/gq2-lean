/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcC6WeightedTracePrefix

/-!
Checked low-weight collection after `MpcC6WeightedTracePrefix`.  The trace uses only the
existing exact checker rules.  It erases the restricted-square triple, the same-generator
power commutator `[B,B^4]`, and the remaining `[C,B^2]` restricted-square pair.  The resulting
47-factor endpoint lies entirely in depth five.  No class-five relation or Jacobi reduction is
claimed here.
-/

namespace GQ2.Dyadic.Instances.MpcC6WeightedTraceLow

open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord

private def w0 : CWord := (.gen .D)
private def w1 : CWord := (.gen .B)
private def w2 : CWord := (.comm w0 w1)
private def w3 : CWord := (.sq w2)
private def w4 : CWord := (.gen .A)
private def w5 : CWord := (.sq w1)
private def w6 : CWord := (.sq w5)
private def w7 : CWord := (.comm w4 w6)
private def w8 : CWord := (.sq w7)
private def w9 : CWord := (.comm w2 w4)
private def w10 : CWord := (.comm w9 w2)
private def w11 : CWord := (.comm w2 w1)
private def w12 : CWord := (.comm w1 w6)
private def w13 : CWord := (.comm w4 w1)
private def w14 : CWord := (.comm w13 w2)
private def w15 : CWord := (.sq w14)
private def w16 : CWord := (.comm w2 w6)
private def w17 : CWord := (.comm w4 w2)
private def w18 : CWord := (.comm w17 w2)
private def w19 : CWord := (.comm w11 w2)
private def w20 : CWord := (.comm w17 w13)
private def w21 : CWord := (.gen .C)
private def w22 : CWord := (.comm w21 w5)
private def w23 : CWord := (.sq w22)
private def w24 : CWord := (.sq w21)
private def w25 : CWord := (.comm w24 w6)
private def w26 : CWord := (.comm w22 w24)
private def w27 : CWord := (.comm w22 w21)
private def w28 : CWord := (.sq w27)
private def w29 : CWord := (.comm w21 w6)
private def w30 : CWord := (.comm w5 w0)
private def w31 : CWord := (.comm w5 w30)
private def w32 : CWord := (.comm w5 w6)
private def w33 : CWord := (.comm w21 w0)
private def w34 : CWord := (.comm w33 w6)
private def w35 : CWord := (.comm w3 w33)
private def w36 : CWord := (.comm w3 w13)
private def w37 : CWord := (.comm w9 w33)
private def w38 : CWord := (.comm w9 w13)
private def w39 : CWord := (.comm w17 w33)
private def w40 : CWord := (.comm w11 w33)
private def w41 : CWord := (.comm w1 w0)
private def w42 : CWord := (.comm w41 w4)
private def w43 : CWord := (.sq w42)
private def w44 : CWord := (.sq w43)
private def w45 : CWord := (.comm w5 w4)
private def w46 : CWord := (.sq w45)
private def w47 : CWord := (.sq w46)
private def w48 : CWord := (.comm w1 w21)
private def w49 : CWord := (.comm w48 w1)
private def w50 : CWord := (.sq w49)
private def w51 : CWord := (.sq w50)
private def w52 : CWord := (.comm w41 w1)
private def w53 : CWord := (.comm w52 w4)
private def w54 : CWord := (.sq w53)
private def w55 : CWord := (.comm w49 w1)
private def w56 : CWord := (.sq w55)
private def w57 : CWord := (.comm w52 w1)
private def w58 : CWord := (.sq w57)
private def w59 : CWord := (.comm w41 w0)
private def w60 : CWord := (.comm w59 w1)
private def w61 : CWord := (.sq w60)
private def w62 : CWord := (.comm w43 w4)
private def w63 : CWord := (.comm w46 w4)
private def w64 : CWord := (.comm w53 w4)
private def w65 : CWord := (.comm w57 w4)
private def w66 : CWord := (.comm w43 w1)
private def w67 : CWord := (.comm w46 w1)
private def w68 : CWord := (.comm w50 w1)
private def w69 : CWord := (.comm w53 w1)
private def w70 : CWord := (.comm w55 w1)
private def w71 : CWord := (.comm w57 w1)
private def w72 : CWord := (.comm w60 w1)
private def w73 : CWord := (.sq w52)
private def w74 : CWord := (.comm w73 w0)
private def w75 : CWord := (.comm w57 w0)
private def w76 : CWord := (.comm w4 w73)
private def w77 : CWord := (.sq w6)
private def w78 : CWord := (.comm w4 w77)
private def w79 : CWord := (.comm w48 w21)
private def w80 : CWord := (.comm w79 w1)
private def w81 : CWord := (.comm w21 w80)
private def w82 : CWord := (.sq w79)
private def w83 : CWord := (.comm w21 w82)
private def w84 : CWord := (.comm w21 w50)
private def w85 : CWord := (.sq w48)
private def w86 : CWord := (.sq w85)
private def w87 : CWord := (.comm w21 w86)
private def w88 : CWord := (.mul w84 w87)
private def w89 : CWord := (.mul w83 w88)
private def w90 : CWord := (.mul w81 w89)
private def w91 : CWord := (.mul w78 w90)
private def w92 : CWord := (.mul w76 w91)
private def w93 : CWord := (.mul w75 w92)
private def w94 : CWord := (.mul w74 w93)
private def w95 : CWord := (.mul w72 w94)
private def w96 : CWord := (.mul w71 w95)
private def w97 : CWord := (.mul w70 w96)
private def w98 : CWord := (.mul w69 w97)
private def w99 : CWord := (.mul w68 w98)
private def w100 : CWord := (.mul w67 w99)
private def w101 : CWord := (.mul w66 w100)
private def w102 : CWord := (.mul w65 w101)
private def w103 : CWord := (.mul w64 w102)
private def w104 : CWord := (.mul w63 w103)
private def w105 : CWord := (.mul w62 w104)
private def w106 : CWord := (.mul w61 w105)
private def w107 : CWord := (.mul w58 w106)
private def w108 : CWord := (.mul w56 w107)
private def w109 : CWord := (.mul w54 w108)
private def w110 : CWord := (.mul w51 w109)
private def w111 : CWord := (.mul w47 w110)
private def w112 : CWord := (.mul w44 w111)
private def w113 : CWord := (.mul w40 w112)
private def w114 : CWord := (.mul w39 w113)
private def w115 : CWord := (.mul w38 w114)
private def w116 : CWord := (.mul w37 w115)
private def w117 : CWord := (.mul w36 w116)
private def w118 : CWord := (.mul w35 w117)
private def w119 : CWord := (.mul w34 w118)
private def w120 : CWord := (.mul w32 w119)
private def w121 : CWord := (.mul w31 w120)
private def w122 : CWord := (.mul w30 w121)
private def w123 : CWord := (.mul w29 w122)
private def w124 : CWord := (.mul w28 w123)
private def w125 : CWord := (.mul w26 w124)
private def w126 : CWord := (.mul w25 w125)
private def w127 : CWord := (.mul w23 w126)
private def w128 : CWord := (.mul w20 w127)
private def w129 : CWord := (.mul w19 w128)
private def w130 : CWord := (.mul w18 w129)
private def w131 : CWord := (.mul w16 w130)
private def w132 : CWord := (.mul w15 w131)
private def w133 : CWord := (.mul w12 w132)
private def w134 : CWord := (.mul w11 w133)
private def w135 : CWord := (.mul w10 w134)
private def w136 : CWord := (.mul w8 w135)
private def w137 : CWord := (.mul w3 w136)
private def w138 : CWord := (.comm w10 w11)
private def w139 : CWord := (.mul w11 w10)
private def w140 : CWord := (.mul w10 w133)
private def w141 : CWord := (.comm w8 w11)
private def w142 : CWord := (.mul w11 w8)
private def w143 : CWord := (.comm w29 w30)
private def w144 : CWord := (.mul w30 w29)
private def w145 : CWord := (.mul w29 w121)
private def w146 : CWord := (.comm w28 w30)
private def w147 : CWord := (.mul w30 w28)
private def w148 : CWord := (.mul w28 w145)
private def w149 : CWord := (.comm w26 w30)
private def w150 : CWord := (.mul w30 w26)
private def w151 : CWord := (.mul w26 w148)
private def w152 : CWord := (.comm w25 w30)
private def w153 : CWord := (.mul w30 w25)
private def w154 : CWord := (.mul w25 w151)
private def w155 : CWord := (.comm w23 w30)
private def w156 : CWord := (.mul w30 w23)
private def w157 : CWord := (.mul w23 w154)
private def w158 : CWord := (.comm w20 w30)
private def w159 : CWord := (.mul w30 w20)
private def w160 : CWord := (.mul w20 w157)
private def w161 : CWord := (.comm w19 w30)
private def w162 : CWord := (.mul w30 w19)
private def w163 : CWord := (.mul w19 w160)
private def w164 : CWord := (.comm w18 w30)
private def w165 : CWord := (.mul w30 w18)
private def w166 : CWord := (.mul w18 w163)
private def w167 : CWord := (.comm w16 w30)
private def w168 : CWord := (.mul w30 w16)
private def w169 : CWord := (.mul w16 w166)
private def w170 : CWord := (.comm w15 w30)
private def w171 : CWord := (.mul w30 w15)
private def w172 : CWord := (.mul w15 w169)
private def w173 : CWord := (.comm w12 w30)
private def w174 : CWord := (.mul w30 w12)
private def w175 : CWord := (.mul w12 w172)
private def w176 : CWord := (.comm w10 w30)
private def w177 : CWord := (.mul w30 w10)
private def w178 : CWord := (.mul w10 w175)
private def w179 : CWord := (.comm w8 w30)
private def w180 : CWord := (.mul w30 w8)
private def w181 : CWord := (.mul w8 w178)
private def w182 : CWord := (.mul w11 w30)
private def w183 : CWord := (.inv w2)
private def w184 : CWord := (.inv w11)
private def w185 : CWord := (.comm w184 w183)
private def w186 : CWord := (.mul w184 w185)
private def w187 : CWord := (.mul w185 w183)
private def w188 : CWord := (.mul w184 w187)
private def w189 : CWord := (.mul w183 w188)
private def w190 : CWord := (.mul w11 w189)
private def w191 : CWord := (.mul w183 w11)
private def w192 : CWord := (.comm w11 w183)
private def w193 : CWord := (.mul w192 w188)
private def w194 : CWord := (.mul w11 w193)
private def w195 : CWord := (.comm w192 w184)
private def w196 : CWord := (.mul w184 w192)
private def w197 : CWord := (.mul w192 w187)
private def w198 : CWord := (.comm w185 w183)
private def w199 : CWord := (.mul w183 w185)
private def w200 : CWord := (.comm w192 w183)
private def w201 : CWord := (.mul w183 w192)
private def w202 : CWord := (.mul w192 w185)
private def w203 : CWord := (.inv w192)
private def w204 : CWord := (.comm w203 w184)
private def w205 : CWord := .one
private def w206 : CWord := (.mul w205 w205)
private def w207 : CWord := (.comm w205 w1)
private def w208 : CWord := (.comm w205 w5)
private def w209 : CWord := (.mul w206 w208)
private def w210 : CWord := (.comm w28 w29)
private def w211 : CWord := (.mul w29 w28)
private def w212 : CWord := (.mul w28 w121)
private def w213 : CWord := (.comm w26 w29)
private def w214 : CWord := (.mul w29 w26)
private def w215 : CWord := (.mul w26 w212)
private def w216 : CWord := (.comm w25 w29)
private def w217 : CWord := (.mul w29 w25)
private def w218 : CWord := (.mul w25 w215)
private def w219 : CWord := (.comm w6 w21)
private def w220 : CWord := (.inv w219)
private def w221 : CWord := (.comm w22 w5)
private def w222 : CWord := (.inv w22)
private def w223 : CWord := (.inv w221)
private def w224 : CWord := (.comm w223 w222)
private def w225 : CWord := (.mul w223 w224)
private def w226 : CWord := (.mul w224 w222)
private def w227 : CWord := (.mul w223 w226)
private def w228 : CWord := (.mul w222 w227)
private def w229 : CWord := (.mul w221 w228)
private def w230 : CWord := (.mul w222 w221)
private def w231 : CWord := (.comm w221 w222)
private def w232 : CWord := (.mul w231 w227)
private def w233 : CWord := (.mul w221 w232)
private def w234 : CWord := (.comm w231 w223)
private def w235 : CWord := (.mul w223 w231)
private def w236 : CWord := (.mul w231 w226)
private def w237 : CWord := (.comm w224 w222)
private def w238 : CWord := (.mul w222 w224)
private def w239 : CWord := (.comm w231 w222)
private def w240 : CWord := (.mul w222 w231)
private def w241 : CWord := (.mul w231 w224)
private def w242 : CWord := (.inv w231)
private def w243 : CWord := (.comm w242 w223)
private def w244 : CWord := (.mul w23 w221)
private def w245 : CWord := (.sq w23)

private def trace0 : Deriv :=
  (.refl w137)

private theorem trace0_checked : trace0.check = true := by decide

private theorem trace0_sound :
    eval dmModel.val trace0.lhs = eval dmModel.val trace0.rhs :=
  Deriv.sound dmModel trace0 trace0_checked

private def trace1 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w8)
      (.trans
        (.trans
          (.trans
            (.symm
              (.assoc w10 w11 w133)
            )
            (.mul
              (.swap w10 w11)
              (.refl w133)
            )
          )
          (.mul
            (.trans
              (.mul
                (.mul
                  (.refl w11)
                  (.refl w10)
                )
                (.deep w138)
              )
              (.mul_one w139)
            )
            (.refl w133)
          )
        )
        (.assoc w11 w10 w133)
      )
    )
  )

private theorem trace1_checked : trace1.check = true := by decide

private theorem trace1_sound :
    eval dmModel.val trace1.lhs = eval dmModel.val trace1.rhs :=
  Deriv.sound dmModel trace1 trace1_checked

private def trace2 : Deriv :=
  (.mul
    (.refl w3)
    (.trans
      (.trans
        (.trans
          (.symm
            (.assoc w8 w11 w140)
          )
          (.mul
            (.swap w8 w11)
            (.refl w140)
          )
        )
        (.mul
          (.trans
            (.mul
              (.mul
                (.refl w11)
                (.refl w8)
              )
              (.deep w141)
            )
            (.mul_one w142)
          )
          (.refl w140)
        )
      )
      (.assoc w11 w8 w140)
    )
  )

private theorem trace2_checked : trace2.check = true := by decide

private theorem trace2_sound :
    eval dmModel.val trace2.lhs = eval dmModel.val trace2.rhs :=
  Deriv.sound dmModel trace2 trace2_checked

private def trace3 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.mul
                    (.refl w19)
                    (.mul
                      (.refl w20)
                      (.mul
                        (.refl w23)
                        (.mul
                        (.refl w25)
                        (.mul
                        (.refl w26)
                        (.mul
                        (.refl w28)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w29 w30 w121)
                        )
                        (.mul
                        (.swap w29 w30)
                        (.refl w121)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w29)
                        )
                        (.deep w143)
                        )
                        (.mul_one w144)
                        )
                        (.refl w121)
                        )
                        )
                        (.assoc w30 w29 w121)
                        )
                        )
                        )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace3_checked : trace3.check = true := by decide

private theorem trace3_sound :
    eval dmModel.val trace3.lhs = eval dmModel.val trace3.rhs :=
  Deriv.sound dmModel trace3 trace3_checked

private def trace4 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.mul
                    (.refl w19)
                    (.mul
                      (.refl w20)
                      (.mul
                        (.refl w23)
                        (.mul
                        (.refl w25)
                        (.mul
                        (.refl w26)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w28 w30 w145)
                        )
                        (.mul
                        (.swap w28 w30)
                        (.refl w145)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w28)
                        )
                        (.deep w146)
                        )
                        (.mul_one w147)
                        )
                        (.refl w145)
                        )
                        )
                        (.assoc w30 w28 w145)
                        )
                        )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace4_checked : trace4.check = true := by decide

private theorem trace4_sound :
    eval dmModel.val trace4.lhs = eval dmModel.val trace4.rhs :=
  Deriv.sound dmModel trace4 trace4_checked

private def trace5 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.mul
                    (.refl w19)
                    (.mul
                      (.refl w20)
                      (.mul
                        (.refl w23)
                        (.mul
                        (.refl w25)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w26 w30 w148)
                        )
                        (.mul
                        (.swap w26 w30)
                        (.refl w148)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w26)
                        )
                        (.deep w149)
                        )
                        (.mul_one w150)
                        )
                        (.refl w148)
                        )
                        )
                        (.assoc w30 w26 w148)
                        )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace5_checked : trace5.check = true := by decide

private theorem trace5_sound :
    eval dmModel.val trace5.lhs = eval dmModel.val trace5.rhs :=
  Deriv.sound dmModel trace5 trace5_checked

private def trace6 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.mul
                    (.refl w19)
                    (.mul
                      (.refl w20)
                      (.mul
                        (.refl w23)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w25 w30 w151)
                        )
                        (.mul
                        (.swap w25 w30)
                        (.refl w151)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w25)
                        )
                        (.deep w152)
                        )
                        (.mul_one w153)
                        )
                        (.refl w151)
                        )
                        )
                        (.assoc w30 w25 w151)
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace6_checked : trace6.check = true := by decide

private theorem trace6_sound :
    eval dmModel.val trace6.lhs = eval dmModel.val trace6.rhs :=
  Deriv.sound dmModel trace6 trace6_checked

private def trace7 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.mul
                    (.refl w19)
                    (.mul
                      (.refl w20)
                      (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w23 w30 w154)
                        )
                        (.mul
                        (.swap w23 w30)
                        (.refl w154)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w23)
                        )
                        (.deep w155)
                        )
                        (.mul_one w156)
                        )
                        (.refl w154)
                        )
                        )
                        (.assoc w30 w23 w154)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace7_checked : trace7.check = true := by decide

private theorem trace7_sound :
    eval dmModel.val trace7.lhs = eval dmModel.val trace7.rhs :=
  Deriv.sound dmModel trace7 trace7_checked

private def trace8 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.mul
                    (.refl w19)
                    (.trans
                      (.trans
                        (.trans
                        (.symm
                        (.assoc w20 w30 w157)
                        )
                        (.mul
                        (.swap w20 w30)
                        (.refl w157)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w20)
                        )
                        (.deep w158)
                        )
                        (.mul_one w159)
                        )
                        (.refl w157)
                        )
                      )
                      (.assoc w30 w20 w157)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace8_checked : trace8.check = true := by decide

private theorem trace8_sound :
    eval dmModel.val trace8.lhs = eval dmModel.val trace8.rhs :=
  Deriv.sound dmModel trace8 trace8_checked

private def trace9 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.mul
                  (.refl w18)
                  (.trans
                    (.trans
                      (.trans
                        (.symm
                        (.assoc w19 w30 w160)
                        )
                        (.mul
                        (.swap w19 w30)
                        (.refl w160)
                        )
                      )
                      (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w19)
                        )
                        (.deep w161)
                        )
                        (.mul_one w162)
                        )
                        (.refl w160)
                      )
                    )
                    (.assoc w30 w19 w160)
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace9_checked : trace9.check = true := by decide

private theorem trace9_sound :
    eval dmModel.val trace9.lhs = eval dmModel.val trace9.rhs :=
  Deriv.sound dmModel trace9 trace9_checked

private def trace10 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.mul
                (.refl w16)
                (.trans
                  (.trans
                    (.trans
                      (.symm
                        (.assoc w18 w30 w163)
                      )
                      (.mul
                        (.swap w18 w30)
                        (.refl w163)
                      )
                    )
                    (.mul
                      (.trans
                        (.mul
                        (.mul
                        (.refl w30)
                        (.refl w18)
                        )
                        (.deep w164)
                        )
                        (.mul_one w165)
                      )
                      (.refl w163)
                    )
                  )
                  (.assoc w30 w18 w163)
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace10_checked : trace10.check = true := by decide

private theorem trace10_sound :
    eval dmModel.val trace10.lhs = eval dmModel.val trace10.rhs :=
  Deriv.sound dmModel trace10 trace10_checked

private def trace11 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.mul
              (.refl w15)
              (.trans
                (.trans
                  (.trans
                    (.symm
                      (.assoc w16 w30 w166)
                    )
                    (.mul
                      (.swap w16 w30)
                      (.refl w166)
                    )
                  )
                  (.mul
                    (.trans
                      (.mul
                        (.mul
                        (.refl w30)
                        (.refl w16)
                        )
                        (.deep w167)
                      )
                      (.mul_one w168)
                    )
                    (.refl w166)
                  )
                )
                (.assoc w30 w16 w166)
              )
            )
          )
        )
      )
    )
  )

private theorem trace11_checked : trace11.check = true := by decide

private theorem trace11_sound :
    eval dmModel.val trace11.lhs = eval dmModel.val trace11.rhs :=
  Deriv.sound dmModel trace11 trace11_checked

private def trace12 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.mul
            (.refl w12)
            (.trans
              (.trans
                (.trans
                  (.symm
                    (.assoc w15 w30 w169)
                  )
                  (.mul
                    (.swap w15 w30)
                    (.refl w169)
                  )
                )
                (.mul
                  (.trans
                    (.mul
                      (.mul
                        (.refl w30)
                        (.refl w15)
                      )
                      (.deep w170)
                    )
                    (.mul_one w171)
                  )
                  (.refl w169)
                )
              )
              (.assoc w30 w15 w169)
            )
          )
        )
      )
    )
  )

private theorem trace12_checked : trace12.check = true := by decide

private theorem trace12_sound :
    eval dmModel.val trace12.lhs = eval dmModel.val trace12.rhs :=
  Deriv.sound dmModel trace12 trace12_checked

private def trace13 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.mul
          (.refl w10)
          (.trans
            (.trans
              (.trans
                (.symm
                  (.assoc w12 w30 w172)
                )
                (.mul
                  (.swap w12 w30)
                  (.refl w172)
                )
              )
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.refl w30)
                      (.refl w12)
                    )
                    (.deep w173)
                  )
                  (.mul_one w174)
                )
                (.refl w172)
              )
            )
            (.assoc w30 w12 w172)
          )
        )
      )
    )
  )

private theorem trace13_checked : trace13.check = true := by decide

private theorem trace13_sound :
    eval dmModel.val trace13.lhs = eval dmModel.val trace13.rhs :=
  Deriv.sound dmModel trace13 trace13_checked

private def trace14 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.mul
        (.refl w8)
        (.trans
          (.trans
            (.trans
              (.symm
                (.assoc w10 w30 w175)
              )
              (.mul
                (.swap w10 w30)
                (.refl w175)
              )
            )
            (.mul
              (.trans
                (.mul
                  (.mul
                    (.refl w30)
                    (.refl w10)
                  )
                  (.deep w176)
                )
                (.mul_one w177)
              )
              (.refl w175)
            )
          )
          (.assoc w30 w10 w175)
        )
      )
    )
  )

private theorem trace14_checked : trace14.check = true := by decide

private theorem trace14_sound :
    eval dmModel.val trace14.lhs = eval dmModel.val trace14.rhs :=
  Deriv.sound dmModel trace14 trace14_checked

private def trace15 : Deriv :=
  (.mul
    (.refl w3)
    (.mul
      (.refl w11)
      (.trans
        (.trans
          (.trans
            (.symm
              (.assoc w8 w30 w178)
            )
            (.mul
              (.swap w8 w30)
              (.refl w178)
            )
          )
          (.mul
            (.trans
              (.mul
                (.mul
                  (.refl w30)
                  (.refl w8)
                )
                (.deep w179)
              )
              (.mul_one w180)
            )
            (.refl w178)
          )
        )
        (.assoc w30 w8 w178)
      )
    )
  )

private theorem trace15_checked : trace15.check = true := by decide

private theorem trace15_sound :
    eval dmModel.val trace15.lhs = eval dmModel.val trace15.rhs :=
  Deriv.sound dmModel trace15 trace15_checked

private def trace16 : Deriv :=
  (.mul
    (.refl w3)
    (.symm
      (.assoc w11 w30 w181)
    )
  )

private theorem trace16_checked : trace16.check = true := by decide

private theorem trace16_sound :
    eval dmModel.val trace16.lhs = eval dmModel.val trace16.rhs :=
  Deriv.sound dmModel trace16 trace16_checked

private def trace17 : Deriv :=
  (.symm
    (.assoc w3 w182 w181)
  )

private theorem trace17_checked : trace17.check = true := by decide

private theorem trace17_sound :
    eval dmModel.val trace17.lhs = eval dmModel.val trace17.rhs :=
  Deriv.sound dmModel trace17 trace17_checked

private def trace18 : Deriv :=
  (.mul
    (.trans
      (.trans
        (.trans
          (.trans
            (.trans
              (.trans
                (.trans
                  (.trans
                    (.trans
                      (.trans
                        (.trans
                        (.trans
                        (.mul
                        (.refl w3)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.trans
                        (.trans
                        (.comm
                        (.symm
                        (.mul_self w1)
                        )
                        (.refl w0)
                        )
                        (.comm_mul_left w1 w1 w0)
                        )
                        (.mul
                        (.mul
                        (.symm
                        (.inv_comm w0 w1)
                        )
                        (.comm
                        (.symm
                        (.inv_comm w0 w1)
                        )
                        (.refl w1)
                        )
                        )
                        (.symm
                        (.inv_comm w0 w1)
                        )
                        )
                        )
                        (.mul
                        (.mul
                        (.refl w183)
                        (.comm_inv_left w2 w1)
                        )
                        (.refl w183)
                        )
                        )
                        )
                        )
                        (.mul
                        (.refl w3)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.mul
                        (.mul
                        (.refl w183)
                        (.mul
                        (.refl w184)
                        (.refl w185)
                        )
                        )
                        (.refl w183)
                        )
                        (.trans
                        (.assoc w183 w186 w183)
                        (.mul
                        (.refl w183)
                        (.trans
                        (.assoc w184 w185 w183)
                        (.mul
                        (.refl w184)
                        (.refl w187)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.trans
                        (.mul
                        (.symm
                        (.mul_self w2)
                        )
                        (.refl w190)
                        )
                        (.assoc w2 w2 w190)
                        )
                        )
                        (.mul
                        (.refl w2)
                        (.mul
                        (.refl w2)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w11 w183 w188)
                        )
                        (.mul
                        (.swap w11 w183)
                        (.refl w188)
                        )
                        )
                        (.assoc w191 w192 w188)
                        )
                        (.assoc w183 w11 w193)
                        )
                        )
                        )
                      )
                      (.mul
                        (.refl w2)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w2 w183 w194)
                        )
                        (.mul
                        (.mul_inv w2)
                        (.refl w194)
                        )
                        )
                        (.one_mul w194)
                        )
                      )
                    )
                    (.mul
                      (.refl w2)
                      (.mul
                        (.refl w11)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w192 w184 w187)
                        )
                        (.mul
                        (.swap w192 w184)
                        (.refl w187)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w184)
                        (.refl w192)
                        )
                        (.deep w195)
                        )
                        (.mul_one w196)
                        )
                        (.refl w187)
                        )
                        )
                        (.assoc w184 w192 w187)
                        )
                      )
                    )
                  )
                  (.mul
                    (.refl w2)
                    (.trans
                      (.trans
                        (.symm
                        (.assoc w11 w184 w197)
                        )
                        (.mul
                        (.mul_inv w11)
                        (.refl w197)
                        )
                      )
                      (.one_mul w197)
                    )
                  )
                )
                (.mul
                  (.refl w2)
                  (.mul
                    (.refl w192)
                    (.trans
                      (.swap w185 w183)
                      (.trans
                        (.mul
                        (.mul
                        (.refl w183)
                        (.refl w185)
                        )
                        (.deep w198)
                        )
                        (.mul_one w199)
                      )
                    )
                  )
                )
              )
              (.mul
                (.refl w2)
                (.trans
                  (.trans
                    (.trans
                      (.symm
                        (.assoc w192 w183 w185)
                      )
                      (.mul
                        (.swap w192 w183)
                        (.refl w185)
                      )
                    )
                    (.mul
                      (.trans
                        (.mul
                        (.mul
                        (.refl w183)
                        (.refl w192)
                        )
                        (.deep w200)
                        )
                        (.mul_one w201)
                      )
                      (.refl w185)
                    )
                  )
                  (.assoc w183 w192 w185)
                )
              )
            )
            (.trans
              (.trans
                (.symm
                  (.assoc w2 w183 w202)
                )
                (.mul
                  (.mul_inv w2)
                  (.refl w202)
                )
              )
              (.one_mul w202)
            )
          )
          (.mul
            (.refl w192)
            (.comm_inv_left w11 w183)
          )
        )
        (.trans
          (.trans
            (.symm
              (.assoc w192 w203 w204)
            )
            (.mul
              (.mul_inv w192)
              (.refl w204)
            )
          )
          (.one_mul w204)
        )
      )
      (.deep w204)
    )
    (.refl w181)
  )

private theorem trace18_checked : trace18.check = true := by decide

private theorem trace18_sound :
    eval dmModel.val trace18.lhs = eval dmModel.val trace18.rhs :=
  Deriv.sound dmModel trace18 trace18_checked

private def trace19 : Deriv :=
  (.one_mul w181)

private theorem trace19_checked : trace19.check = true := by decide

private theorem trace19_sound :
    eval dmModel.val trace19.lhs = eval dmModel.val trace19.rhs :=
  Deriv.sound dmModel trace19 trace19_checked

private def trace20 : Deriv :=
  (.mul
    (.refl w8)
    (.mul
      (.refl w10)
      (.trans
        (.mul
          (.trans
            (.trans
              (.trans
                (.comm
                  (.refl w1)
                  (.symm
                    (.mul_self w5)
                  )
                )
                (.comm_mul_right w1 w5 w5)
              )
              (.mul
                (.mul
                  (.trans
                    (.trans
                      (.comm
                        (.refl w1)
                        (.symm
                        (.mul_self w1)
                        )
                      )
                      (.comm_mul_right w1 w1 w1)
                    )
                    (.trans
                      (.mul
                        (.trans
                        (.mul
                        (.comm_self w1)
                        (.comm_self w1)
                        )
                        (.deep w206)
                        )
                        (.trans
                        (.comm
                        (.comm_self w1)
                        (.refl w1)
                        )
                        (.deep w207)
                        )
                      )
                      (.deep w206)
                    )
                  )
                  (.trans
                    (.trans
                      (.comm
                        (.refl w1)
                        (.symm
                        (.mul_self w1)
                        )
                      )
                      (.comm_mul_right w1 w1 w1)
                    )
                    (.trans
                      (.mul
                        (.trans
                        (.mul
                        (.comm_self w1)
                        (.comm_self w1)
                        )
                        (.deep w206)
                        )
                        (.trans
                        (.comm
                        (.comm_self w1)
                        (.refl w1)
                        )
                        (.deep w207)
                        )
                      )
                      (.deep w206)
                    )
                  )
                )
                (.comm
                  (.trans
                    (.trans
                      (.comm
                        (.refl w1)
                        (.symm
                        (.mul_self w1)
                        )
                      )
                      (.comm_mul_right w1 w1 w1)
                    )
                    (.trans
                      (.mul
                        (.trans
                        (.mul
                        (.comm_self w1)
                        (.comm_self w1)
                        )
                        (.deep w206)
                        )
                        (.trans
                        (.comm
                        (.comm_self w1)
                        (.refl w1)
                        )
                        (.deep w207)
                        )
                      )
                      (.deep w206)
                    )
                  )
                  (.refl w5)
                )
              )
            )
            (.deep w209)
          )
          (.refl w172)
        )
        (.one_mul w172)
      )
    )
  )

private theorem trace20_checked : trace20.check = true := by decide

private theorem trace20_sound :
    eval dmModel.val trace20.lhs = eval dmModel.val trace20.rhs :=
  Deriv.sound dmModel trace20 trace20_checked

private def trace21 : Deriv :=
  (.mul
    (.refl w8)
    (.mul
      (.refl w10)
      (.mul
        (.refl w15)
        (.mul
          (.refl w16)
          (.mul
            (.refl w18)
            (.mul
              (.refl w19)
              (.mul
                (.refl w20)
                (.mul
                  (.refl w23)
                  (.mul
                    (.refl w25)
                    (.mul
                      (.refl w26)
                      (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w28 w29 w121)
                        )
                        (.mul
                        (.swap w28 w29)
                        (.refl w121)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w29)
                        (.refl w28)
                        )
                        (.deep w210)
                        )
                        (.mul_one w211)
                        )
                        (.refl w121)
                        )
                        )
                        (.assoc w29 w28 w121)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace21_checked : trace21.check = true := by decide

private theorem trace21_sound :
    eval dmModel.val trace21.lhs = eval dmModel.val trace21.rhs :=
  Deriv.sound dmModel trace21 trace21_checked

private def trace22 : Deriv :=
  (.mul
    (.refl w8)
    (.mul
      (.refl w10)
      (.mul
        (.refl w15)
        (.mul
          (.refl w16)
          (.mul
            (.refl w18)
            (.mul
              (.refl w19)
              (.mul
                (.refl w20)
                (.mul
                  (.refl w23)
                  (.mul
                    (.refl w25)
                    (.trans
                      (.trans
                        (.trans
                        (.symm
                        (.assoc w26 w29 w212)
                        )
                        (.mul
                        (.swap w26 w29)
                        (.refl w212)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w29)
                        (.refl w26)
                        )
                        (.deep w213)
                        )
                        (.mul_one w214)
                        )
                        (.refl w212)
                        )
                      )
                      (.assoc w29 w26 w212)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace22_checked : trace22.check = true := by decide

private theorem trace22_sound :
    eval dmModel.val trace22.lhs = eval dmModel.val trace22.rhs :=
  Deriv.sound dmModel trace22 trace22_checked

private def trace23 : Deriv :=
  (.mul
    (.refl w8)
    (.mul
      (.refl w10)
      (.mul
        (.refl w15)
        (.mul
          (.refl w16)
          (.mul
            (.refl w18)
            (.mul
              (.refl w19)
              (.mul
                (.refl w20)
                (.mul
                  (.refl w23)
                  (.trans
                    (.trans
                      (.trans
                        (.symm
                        (.assoc w25 w29 w215)
                        )
                        (.mul
                        (.swap w25 w29)
                        (.refl w215)
                        )
                      )
                      (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w29)
                        (.refl w25)
                        )
                        (.deep w216)
                        )
                        (.mul_one w217)
                        )
                        (.refl w215)
                      )
                    )
                    (.assoc w29 w25 w215)
                  )
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace23_checked : trace23.check = true := by decide

private theorem trace23_sound :
    eval dmModel.val trace23.lhs = eval dmModel.val trace23.rhs :=
  Deriv.sound dmModel trace23 trace23_checked

private def trace24 : Deriv :=
  (.mul
    (.refl w8)
    (.mul
      (.refl w10)
      (.mul
        (.refl w15)
        (.mul
          (.refl w16)
          (.mul
            (.refl w18)
            (.mul
              (.refl w19)
              (.mul
                (.refl w20)
                (.trans
                  (.trans
                    (.symm
                      (.assoc w23 w29 w218)
                    )
                    (.mul
                      (.trans
                        (.trans
                        (.trans
                        (.mul
                        (.refl w23)
                        (.symm
                        (.inv_comm w6 w21)
                        )
                        )
                        (.mul
                        (.refl w23)
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.one_mul w220)
                        )
                        (.mul
                        (.symm
                        (.trans
                        (.assoc w23 w221 w219)
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.trans
                        (.mul
                        (.refl w23)
                        (.mul
                        (.refl w221)
                        (.trans
                        (.trans
                        (.trans
                        (.comm
                        (.symm
                        (.mul_self w5)
                        )
                        (.refl w21)
                        )
                        (.comm_mul_left w5 w5 w21)
                        )
                        (.mul
                        (.mul
                        (.symm
                        (.inv_comm w21 w5)
                        )
                        (.comm
                        (.symm
                        (.inv_comm w21 w5)
                        )
                        (.refl w5)
                        )
                        )
                        (.symm
                        (.inv_comm w21 w5)
                        )
                        )
                        )
                        (.mul
                        (.mul
                        (.refl w222)
                        (.comm_inv_left w22 w5)
                        )
                        (.refl w222)
                        )
                        )
                        )
                        )
                        (.mul
                        (.refl w23)
                        (.mul
                        (.refl w221)
                        (.trans
                        (.mul
                        (.mul
                        (.refl w222)
                        (.mul
                        (.refl w223)
                        (.refl w224)
                        )
                        )
                        (.refl w222)
                        )
                        (.trans
                        (.assoc w222 w225 w222)
                        (.mul
                        (.refl w222)
                        (.trans
                        (.assoc w223 w224 w222)
                        (.mul
                        (.refl w223)
                        (.refl w226)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.trans
                        (.mul
                        (.symm
                        (.mul_self w22)
                        )
                        (.refl w229)
                        )
                        (.assoc w22 w22 w229)
                        )
                        )
                        (.mul
                        (.refl w22)
                        (.mul
                        (.refl w22)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w221 w222 w227)
                        )
                        (.mul
                        (.swap w221 w222)
                        (.refl w227)
                        )
                        )
                        (.assoc w230 w231 w227)
                        )
                        (.assoc w222 w221 w232)
                        )
                        )
                        )
                        )
                        (.mul
                        (.refl w22)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w22 w222 w233)
                        )
                        (.mul
                        (.mul_inv w22)
                        (.refl w233)
                        )
                        )
                        (.one_mul w233)
                        )
                        )
                        )
                        (.mul
                        (.refl w22)
                        (.mul
                        (.refl w221)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w231 w223 w226)
                        )
                        (.mul
                        (.swap w231 w223)
                        (.refl w226)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w223)
                        (.refl w231)
                        )
                        (.deep w234)
                        )
                        (.mul_one w235)
                        )
                        (.refl w226)
                        )
                        )
                        (.assoc w223 w231 w226)
                        )
                        )
                        )
                        )
                        (.mul
                        (.refl w22)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w221 w223 w236)
                        )
                        (.mul
                        (.mul_inv w221)
                        (.refl w236)
                        )
                        )
                        (.one_mul w236)
                        )
                        )
                        )
                        (.mul
                        (.refl w22)
                        (.mul
                        (.refl w231)
                        (.trans
                        (.swap w224 w222)
                        (.trans
                        (.mul
                        (.mul
                        (.refl w222)
                        (.refl w224)
                        )
                        (.deep w237)
                        )
                        (.mul_one w238)
                        )
                        )
                        )
                        )
                        )
                        (.mul
                        (.refl w22)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w231 w222 w224)
                        )
                        (.mul
                        (.swap w231 w222)
                        (.refl w224)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w222)
                        (.refl w231)
                        )
                        (.deep w239)
                        )
                        (.mul_one w240)
                        )
                        (.refl w224)
                        )
                        )
                        (.assoc w222 w231 w224)
                        )
                        )
                        )
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w22 w222 w241)
                        )
                        (.mul
                        (.mul_inv w22)
                        (.refl w241)
                        )
                        )
                        (.one_mul w241)
                        )
                        )
                        (.mul
                        (.refl w231)
                        (.comm_inv_left w221 w222)
                        )
                        )
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w231 w242 w243)
                        )
                        (.mul
                        (.mul_inv w231)
                        (.refl w243)
                        )
                        )
                        (.one_mul w243)
                        )
                        )
                        (.deep w243)
                        )
                        )
                        )
                        (.refl w220)
                        )
                        )
                        (.assoc w244 w219 w220)
                        )
                        (.mul
                        (.refl w244)
                        (.mul_inv w219)
                        )
                        )
                        (.mul_one w244)
                        )
                        )
                        )
                        (.symm
                        (.assoc w23 w23 w221)
                        )
                        )
                        (.mul
                        (.mul_self w23)
                        (.refl w221)
                        )
                      )
                      (.refl w218)
                    )
                  )
                  (.assoc w245 w221 w218)
                )
              )
            )
          )
        )
      )
    )
  )

private theorem trace24_checked : trace24.check = true := by decide

private theorem trace24_sound :
    eval dmModel.val trace24.lhs = eval dmModel.val trace24.rhs :=
  Deriv.sound dmModel trace24 trace24_checked

private theorem block0_sound :
    eval dmModel.val trace0.lhs = eval dmModel.val trace7.rhs :=
  calc
    _ = eval dmModel.val trace0.rhs := trace0_sound
    _ = eval dmModel.val trace1.rhs := trace1_sound
    _ = eval dmModel.val trace2.rhs := trace2_sound
    _ = eval dmModel.val trace3.rhs := trace3_sound
    _ = eval dmModel.val trace4.rhs := trace4_sound
    _ = eval dmModel.val trace5.rhs := trace5_sound
    _ = eval dmModel.val trace6.rhs := trace6_sound
    _ = eval dmModel.val trace7.rhs := trace7_sound

private theorem block1_sound :
    eval dmModel.val trace8.lhs = eval dmModel.val trace15.rhs :=
  calc
    _ = eval dmModel.val trace8.rhs := trace8_sound
    _ = eval dmModel.val trace9.rhs := trace9_sound
    _ = eval dmModel.val trace10.rhs := trace10_sound
    _ = eval dmModel.val trace11.rhs := trace11_sound
    _ = eval dmModel.val trace12.rhs := trace12_sound
    _ = eval dmModel.val trace13.rhs := trace13_sound
    _ = eval dmModel.val trace14.rhs := trace14_sound
    _ = eval dmModel.val trace15.rhs := trace15_sound

private theorem block2_sound :
    eval dmModel.val trace16.lhs = eval dmModel.val trace23.rhs :=
  calc
    _ = eval dmModel.val trace16.rhs := trace16_sound
    _ = eval dmModel.val trace17.rhs := trace17_sound
    _ = eval dmModel.val trace18.rhs := trace18_sound
    _ = eval dmModel.val trace19.rhs := trace19_sound
    _ = eval dmModel.val trace20.rhs := trace20_sound
    _ = eval dmModel.val trace21.rhs := trace21_sound
    _ = eval dmModel.val trace22.rhs := trace22_sound
    _ = eval dmModel.val trace23.rhs := trace23_sound

private theorem block3_sound :
    eval dmModel.val trace24.lhs = eval dmModel.val trace24.rhs :=
  calc
    _ = eval dmModel.val trace24.rhs := trace24_sound

def checkedLowTrace : List Deriv :=
  [ trace0, trace1, trace2, trace3, trace4,
    trace5, trace6, trace7, trace8, trace9,
    trace10, trace11, trace12, trace13, trace14,
    trace15, trace16, trace17, trace18, trace19,
    trace20, trace21, trace22, trace23, trace24 ]

theorem checkedLowTrace_all_checked : checkedLowTrace.all Deriv.check = true := by decide

private def startFactors : List CWord :=
  [ w3, w8, w10, w11, w12,
    w15, w16, w18, w19, w20,
    w23, w25, w26, w28, w29,
    w30, w31, w32, w34, w35,
    w36, w37, w38, w39, w40,
    w44, w47, w51, w54, w56,
    w58, w61, w62, w63, w64,
    w65, w66, w67, w68, w69,
    w70, w71, w72, w74, w75,
    w76, w78, w81, w83, w84,
    w87 ]

def endpointFactors : List CWord :=
  [ w8, w10, w15, w16, w18,
    w19, w20, w245, w221, w25,
    w26, w28, w31, w32, w34,
    w35, w36, w37, w38, w39,
    w40, w44, w47, w51, w54,
    w56, w58, w61, w62, w63,
    w64, w65, w66, w67, w68,
    w69, w70, w71, w72, w74,
    w75, w76, w78, w81, w83,
    w84, w87 ]

def endpoint : CWord := trace24.rhs

theorem startFactors_eq_prefix :
    startFactors = MpcC6WeightedTracePrefix.endpointFactors := by decide

theorem endpointFactors_length : endpointFactors.length = 47 := by decide

theorem endpointFactors_all_depth_five :
    endpointFactors.all (fun w => decide (w.depth = 5)) = true := by decide

theorem endpoint_eq_prefix_rightProduct :
    endpoint = MpcC6WeightedTracePrefix.rightProduct endpointFactors := by decide

theorem trace0_lhs_eq_prefix_endpoint :
    trace0.lhs = MpcC6WeightedTracePrefix.endpoint := by
  rw [MpcC6WeightedTracePrefix.endpoint_eq_rightProduct]
  rw [← startFactors_eq_prefix]
  decide

private theorem generatedLowTrace_sound :
    eval dmModel.val trace0.lhs = eval dmModel.val trace24.rhs :=
  calc
    _ = eval dmModel.val trace7.rhs := block0_sound
    _ = eval dmModel.val trace15.rhs := block1_sound
    _ = eval dmModel.val trace23.rhs := block2_sound
    _ = eval dmModel.val trace24.rhs := block3_sound

theorem eval_prefix_endpoint_eq_endpoint :
    eval dmModel.val MpcC6WeightedTracePrefix.endpoint = eval dmModel.val endpoint := by
  rw [← trace0_lhs_eq_prefix_endpoint]
  exact generatedLowTrace_sound

theorem eval_certificateWord_eq_endpoint :
    eval dmModel.val MpcC6WeightedCertificate.Bridge.certificateWord =
      eval dmModel.val endpoint :=
  MpcC6WeightedTracePrefix.eval_certificateWord_eq_endpoint.trans
    eval_prefix_endpoint_eq_endpoint

private def checkedLowBlock0 : Deriv :=
  Deriv.chain [trace0, trace1, trace2, trace3, trace4, trace5, trace6, trace7]

private def checkedLowBlock1 : Deriv :=
  Deriv.chain [trace8, trace9, trace10, trace11, trace12, trace13, trace14, trace15]

private def checkedLowBlock2 : Deriv :=
  Deriv.chain [trace16, trace17, trace18, trace19, trace20, trace21, trace22, trace23]

private def checkedLowBlock3 : Deriv := Deriv.chain [trace24]

private def checkedLowChain : Deriv :=
  Deriv.chain [checkedLowBlock0, checkedLowBlock1, checkedLowBlock2, checkedLowBlock3]

private theorem checkedLowChain_checked : checkedLowChain.check = true := by decide

private theorem checkedLowChain_noRel : checkedLowChain.noRel = true := by decide

private theorem checkedLowChain_lhs :
    checkedLowChain.lhs = MpcC6WeightedTracePrefix.endpoint := by decide

private theorem checkedLowChain_rhs : checkedLowChain.rhs = endpoint := by decide

/-- The low-weight collection uses no presentation relation. -/
theorem eval_prefix_endpoint_eq_endpoint_noRel
    {Q : Type*} [Group Q] (M : DeepModel Q) :
    eval M.val MpcC6WeightedTracePrefix.endpoint = eval M.val endpoint := by
  rw [← checkedLowChain_lhs, ← checkedLowChain_rhs]
  exact Deriv.soundNoRel M checkedLowChain checkedLowChain_checked checkedLowChain_noRel

/-- The complete low-weight prefix is relation-free. -/
theorem eval_certificateWord_eq_endpoint_noRel
    {Q : Type*} [Group Q] (M : DeepModel Q) :
    eval M.val MpcC6WeightedCertificate.Bridge.certificateWord = eval M.val endpoint :=
  (MpcC6WeightedTracePrefix.eval_certificateWord_eq_endpoint_noRel M).trans
    (eval_prefix_endpoint_eq_endpoint_noRel M)

#print axioms checkedLowTrace_all_checked
#print axioms endpointFactors_all_depth_five
#print axioms eval_prefix_endpoint_eq_endpoint
#print axioms eval_certificateWord_eq_endpoint
#print axioms eval_prefix_endpoint_eq_endpoint_noRel
#print axioms eval_certificateWord_eq_endpoint_noRel

end GQ2.Dyadic.Instances.MpcC6WeightedTraceLow
