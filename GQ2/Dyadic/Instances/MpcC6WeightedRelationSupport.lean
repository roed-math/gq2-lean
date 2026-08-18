/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcC6WeightedTraceLow

/-!
The six degree-five consequences of the reflected `mRel`, checked in the weighted collector.
Their free collection contributes 18 depth-five factors.  Appending those factors to the
47-factor low-weight endpoint gives the explicit 65-factor endpoint for the final universal
Hall--Witt/Jacobi cancellation.  This module does not assert that final cancellation.
-/

namespace GQ2.Dyadic.Instances.MpcC6WeightedRelationSupport

open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord

private def w0 : CWord := (.gen .B)
private def w1 : CWord := .one
private def w2 : CWord := (.comm w1 w0)
private def w3 : CWord := (.sq w2)
private def w4 : CWord := (.sq w3)
private def w5 : CWord := (.comm w2 w0)
private def w6 : CWord := (.sq w5)
private def w7 : CWord := (.gen .D)
private def w8 : CWord := (.comm w1 w7)
private def w9 : CWord := (.comm w8 w0)
private def w10 : CWord := (.sq w9)
private def w11 : CWord := (.comm w2 w7)
private def w12 : CWord := (.sq w11)
private def w13 : CWord := (.comm w9 w0)
private def w14 : CWord := (.comm w5 w7)
private def w15 : CWord := (.mul w1 w1)
private def w16 : CWord := (.mul w1 w15)
private def w17 : CWord := (.mul w1 w16)
private def w18 : CWord := (.mul w1 w17)
private def w19 : CWord := (.mul w1 w18)
private def w20 : CWord := (.gen .A)
private def w21 : CWord := (.sq w20)
private def w22 : CWord := (.comm w20 w0)
private def w23 : CWord := (.mul w21 w22)
private def w24 : CWord := (.gen .C)
private def w25 : CWord := (.sq w24)
private def w26 : CWord := (.sq w25)
private def w27 : CWord := (.mul w23 w26)
private def w28 : CWord := (.comm w24 w7)
private def w29 : CWord := (.comm w23 w0)
private def w30 : CWord := (.comm w29 w26)
private def w31 : CWord := (.comm w21 w0)
private def w32 : CWord := (.comm w31 w22)
private def w33 : CWord := (.mul w31 w32)
private def w34 : CWord := (.comm w22 w0)
private def w35 : CWord := (.mul w33 w34)
private def w36 : CWord := (.comm w26 w0)
private def w37 : CWord := (.comm w31 w28)
private def w38 : CWord := (.comm w37 w32)
private def w39 : CWord := (.comm w32 w28)
private def w40 : CWord := (.comm w33 w28)
private def w41 : CWord := (.comm w40 w34)
private def w42 : CWord := (.comm w35 w28)
private def w43 : CWord := (.comm w42 w36)
private def w44 : CWord := (.comm w34 w28)
private def w45 : CWord := (.mul w37 w44)
private def w46 : CWord := (.comm w36 w28)
private def w47 : CWord := (.mul w35 w36)
private def w48 : CWord := (.mul w47 w45)
private def w49 : CWord := (.comm w28 w0)
private def w50 : CWord := (.sq w32)
private def w51 : CWord := (.sq w31)
private def w52 : CWord := (.comm w32 w31)
private def w53 : CWord := (.comm w52 w32)
private def w54 : CWord := (.comm w34 w33)
private def w55 : CWord := (.sq w34)
private def w56 : CWord := (.mul w51 w55)
private def w57 : CWord := (.comm w54 w34)
private def w58 : CWord := (.comm w36 w35)
private def w59 : CWord := (.sq w36)
private def w60 : CWord := (.mul w56 w59)
private def w61 : CWord := (.comm w58 w36)
private def w62 : CWord := (.sq w45)
private def w63 : CWord := (.comm w45 w47)
private def w64 : CWord := (.comm w63 w45)
private def w65 : CWord := (.comm w49 w48)
private def w66 : CWord := (.sq w49)
private def w67 : CWord := (.mul w60 w66)
private def w68 : CWord := (.comm w65 w49)
private def w69 : CWord := (.comm w55 w51)
private def w70 : CWord := (.sq w51)
private def w71 : CWord := (.sq w55)
private def w72 : CWord := (.mul w70 w71)
private def w73 : CWord := (.comm w69 w55)
private def w74 : CWord := (.sq w59)
private def w75 : CWord := (.comm w59 w56)
private def w76 : CWord := (.comm w75 w59)
private def w77 : CWord := (.comm w66 w60)
private def w78 : CWord := (.sq w66)
private def w79 : CWord := (.mul w72 w78)
private def w80 : CWord := (.comm w77 w66)
private def w81 : CWord := (.comm w31 w0)
private def w82 : CWord := (.comm w81 w32)
private def w83 : CWord := (.comm w32 w0)
private def w84 : CWord := (.comm w33 w0)
private def w85 : CWord := (.comm w84 w34)
private def w86 : CWord := (.comm w35 w0)
private def w87 : CWord := (.comm w86 w36)
private def w88 : CWord := (.comm w34 w0)
private def w89 : CWord := (.mul w81 w88)
private def w90 : CWord := (.comm w47 w0)
private def w91 : CWord := (.comm w90 w45)
private def w92 : CWord := (.comm w36 w0)
private def w93 : CWord := (.mul w89 w92)
private def w94 : CWord := (.comm w45 w0)
private def w95 : CWord := (.comm w48 w0)
private def w96 : CWord := (.comm w95 w49)
private def w97 : CWord := (.comm w49 w0)
private def w98 : CWord := (.comm w88 w81)
private def w99 : CWord := (.sq w81)
private def w100 : CWord := (.sq w88)
private def w101 : CWord := (.mul w99 w100)
private def w102 : CWord := (.comm w98 w88)
private def w103 : CWord := (.sq w92)
private def w104 : CWord := (.comm w92 w89)
private def w105 : CWord := (.comm w104 w92)
private def w106 : CWord := (.comm w97 w93)
private def w107 : CWord := (.sq w97)
private def w108 : CWord := (.mul w101 w107)
private def w109 : CWord := (.comm w106 w97)
private def w110 : CWord := (.comm w23 w7)
private def w111 : CWord := (.comm w110 w26)
private def w112 : CWord := (.comm w21 w7)
private def w113 : CWord := (.comm w112 w22)
private def w114 : CWord := (.mul w112 w113)
private def w115 : CWord := (.comm w22 w7)
private def w116 : CWord := (.mul w114 w115)
private def w117 : CWord := (.comm w26 w7)
private def w118 : CWord := (.comm w112 w28)
private def w119 : CWord := (.comm w118 w113)
private def w120 : CWord := (.comm w113 w28)
private def w121 : CWord := (.comm w114 w28)
private def w122 : CWord := (.comm w121 w115)
private def w123 : CWord := (.comm w116 w28)
private def w124 : CWord := (.comm w123 w117)
private def w125 : CWord := (.comm w115 w28)
private def w126 : CWord := (.mul w118 w125)
private def w127 : CWord := (.comm w117 w28)
private def w128 : CWord := (.mul w116 w117)
private def w129 : CWord := (.mul w128 w126)
private def w130 : CWord := (.comm w28 w7)
private def w131 : CWord := (.comm w112 w0)
private def w132 : CWord := (.comm w131 w113)
private def w133 : CWord := (.comm w113 w0)
private def w134 : CWord := (.comm w114 w0)
private def w135 : CWord := (.comm w134 w115)
private def w136 : CWord := (.comm w116 w0)
private def w137 : CWord := (.comm w136 w117)
private def w138 : CWord := (.comm w115 w0)
private def w139 : CWord := (.mul w131 w138)
private def w140 : CWord := (.comm w128 w0)
private def w141 : CWord := (.comm w140 w126)
private def w142 : CWord := (.comm w117 w0)
private def w143 : CWord := (.mul w139 w142)
private def w144 : CWord := (.comm w126 w0)
private def w145 : CWord := (.comm w129 w0)
private def w146 : CWord := (.comm w145 w130)
private def w147 : CWord := (.comm w130 w0)
private def w148 : CWord := (.comm w138 w131)
private def w149 : CWord := (.sq w131)
private def w150 : CWord := (.sq w138)
private def w151 : CWord := (.mul w149 w150)
private def w152 : CWord := (.comm w148 w138)
private def w153 : CWord := (.sq w142)
private def w154 : CWord := (.comm w142 w139)
private def w155 : CWord := (.comm w154 w142)
private def w156 : CWord := (.comm w147 w143)
private def w157 : CWord := (.sq w147)
private def w158 : CWord := (.mul w151 w157)
private def w159 : CWord := (.comm w156 w147)
private def w160 : CWord := (.comm w31 w7)
private def w161 : CWord := (.comm w160 w32)
private def w162 : CWord := (.comm w32 w7)
private def w163 : CWord := (.comm w33 w7)
private def w164 : CWord := (.comm w163 w34)
private def w165 : CWord := (.comm w35 w7)
private def w166 : CWord := (.comm w165 w36)
private def w167 : CWord := (.comm w34 w7)
private def w168 : CWord := (.mul w160 w167)
private def w169 : CWord := (.comm w47 w7)
private def w170 : CWord := (.comm w169 w45)
private def w171 : CWord := (.comm w36 w7)
private def w172 : CWord := (.mul w168 w171)
private def w173 : CWord := (.comm w45 w7)
private def w174 : CWord := (.comm w48 w7)
private def w175 : CWord := (.comm w174 w49)
private def w176 : CWord := (.comm w49 w7)
private def w177 : CWord := (.comm w167 w160)
private def w178 : CWord := (.sq w160)
private def w179 : CWord := (.sq w167)
private def w180 : CWord := (.mul w178 w179)
private def w181 : CWord := (.comm w177 w167)
private def w182 : CWord := (.sq w171)
private def w183 : CWord := (.comm w171 w168)
private def w184 : CWord := (.comm w183 w171)
private def w185 : CWord := (.comm w176 w172)
private def w186 : CWord := (.sq w176)
private def w187 : CWord := (.mul w180 w186)
private def w188 : CWord := (.comm w185 w176)
private def w189 : CWord := (.comm w131 w0)
private def w190 : CWord := (.comm w189 w138)
private def w191 : CWord := (.comm w139 w0)
private def w192 : CWord := (.comm w191 w142)
private def w193 : CWord := (.comm w138 w0)
private def w194 : CWord := (.mul w189 w193)
private def w195 : CWord := (.comm w142 w0)
private def w196 : CWord := (.comm w143 w0)
private def w197 : CWord := (.comm w196 w147)
private def w198 : CWord := (.comm w81 w7)
private def w199 : CWord := (.comm w198 w88)
private def w200 : CWord := (.comm w89 w7)
private def w201 : CWord := (.comm w200 w92)
private def w202 : CWord := (.comm w88 w7)
private def w203 : CWord := (.mul w198 w202)
private def w204 : CWord := (.comm w92 w7)
private def w205 : CWord := (.comm w93 w7)
private def w206 : CWord := (.comm w205 w97)
private def w207 : CWord := (.mul w71 w78)
private def w208 : CWord := (.mul w100 w107)
private def w209 : CWord := (.mul w150 w157)
private def w210 : CWord := (.mul w179 w186)
private def w211 : CWord := (.comm w147 w0)
private def w212 : CWord := (.mul w193 w211)
private def w213 : CWord := (.comm w97 w7)
private def w214 : CWord := (.mul w202 w213)
private def w215 : CWord := (.mul w198 w214)
private def w216 : CWord := (.mul w211 w215)
private def w217 : CWord := (.mul w193 w216)
private def w218 : CWord := (.mul w189 w217)
private def w219 : CWord := (.mul w186 w218)
private def w220 : CWord := (.mul w179 w219)
private def w221 : CWord := (.mul w178 w220)
private def w222 : CWord := (.mul w157 w221)
private def w223 : CWord := (.mul w150 w222)
private def w224 : CWord := (.mul w149 w223)
private def w225 : CWord := (.mul w107 w224)
private def w226 : CWord := (.mul w100 w225)
private def w227 : CWord := (.mul w99 w226)
private def w228 : CWord := (.mul w78 w227)
private def w229 : CWord := (.sq w0)
private def w230 : CWord := (.sq w229)
private def w231 : CWord := (.comm w20 w230)
private def w232 : CWord := (.sq w231)
private def w233 : CWord := (.comm w7 w0)
private def w234 : CWord := (.comm w233 w20)
private def w235 : CWord := (.comm w234 w233)
private def w236 : CWord := (.comm w22 w233)
private def w237 : CWord := (.sq w236)
private def w238 : CWord := (.comm w233 w230)
private def w239 : CWord := (.comm w20 w233)
private def w240 : CWord := (.comm w239 w233)
private def w241 : CWord := (.comm w233 w0)
private def w242 : CWord := (.comm w241 w233)
private def w243 : CWord := (.comm w239 w22)
private def w244 : CWord := (.comm w24 w229)
private def w245 : CWord := (.sq w244)
private def w246 : CWord := (.sq w245)
private def w247 : CWord := (.comm w244 w229)
private def w248 : CWord := (.comm w25 w230)
private def w249 : CWord := (.comm w244 w25)
private def w250 : CWord := (.comm w244 w24)
private def w251 : CWord := (.sq w250)
private def w252 : CWord := (.comm w229 w7)
private def w253 : CWord := (.comm w229 w252)
private def w254 : CWord := (.comm w229 w230)
private def w255 : CWord := (.comm w28 w230)
private def w256 : CWord := (.sq w233)
private def w257 : CWord := (.comm w256 w28)
private def w258 : CWord := (.comm w256 w22)
private def w259 : CWord := (.comm w234 w28)
private def w260 : CWord := (.comm w234 w22)
private def w261 : CWord := (.comm w239 w28)
private def w262 : CWord := (.comm w241 w28)
private def w263 : CWord := (.comm w0 w7)
private def w264 : CWord := (.comm w263 w20)
private def w265 : CWord := (.sq w264)
private def w266 : CWord := (.sq w265)
private def w267 : CWord := (.comm w229 w20)
private def w268 : CWord := (.sq w267)
private def w269 : CWord := (.sq w268)
private def w270 : CWord := (.comm w0 w24)
private def w271 : CWord := (.comm w270 w0)
private def w272 : CWord := (.sq w271)
private def w273 : CWord := (.sq w272)
private def w274 : CWord := (.comm w263 w0)
private def w275 : CWord := (.comm w274 w20)
private def w276 : CWord := (.sq w275)
private def w277 : CWord := (.comm w271 w0)
private def w278 : CWord := (.sq w277)
private def w279 : CWord := (.comm w274 w0)
private def w280 : CWord := (.sq w279)
private def w281 : CWord := (.comm w263 w7)
private def w282 : CWord := (.comm w281 w0)
private def w283 : CWord := (.sq w282)
private def w284 : CWord := (.comm w265 w20)
private def w285 : CWord := (.comm w268 w20)
private def w286 : CWord := (.comm w275 w20)
private def w287 : CWord := (.comm w279 w20)
private def w288 : CWord := (.comm w265 w0)
private def w289 : CWord := (.comm w268 w0)
private def w290 : CWord := (.comm w272 w0)
private def w291 : CWord := (.comm w275 w0)
private def w292 : CWord := (.comm w277 w0)
private def w293 : CWord := (.comm w279 w0)
private def w294 : CWord := (.comm w282 w0)
private def w295 : CWord := (.sq w274)
private def w296 : CWord := (.comm w295 w7)
private def w297 : CWord := (.comm w279 w7)
private def w298 : CWord := (.comm w20 w295)
private def w299 : CWord := (.sq w230)
private def w300 : CWord := (.comm w20 w299)
private def w301 : CWord := (.comm w270 w24)
private def w302 : CWord := (.comm w301 w0)
private def w303 : CWord := (.comm w24 w302)
private def w304 : CWord := (.sq w301)
private def w305 : CWord := (.comm w24 w304)
private def w306 : CWord := (.comm w24 w272)
private def w307 : CWord := (.sq w270)
private def w308 : CWord := (.sq w307)
private def w309 : CWord := (.comm w24 w308)
private def w310 : CWord := (.mul w306 w309)
private def w311 : CWord := (.mul w305 w310)
private def w312 : CWord := (.mul w303 w311)
private def w313 : CWord := (.mul w300 w312)
private def w314 : CWord := (.mul w298 w313)
private def w315 : CWord := (.mul w297 w314)
private def w316 : CWord := (.mul w296 w315)
private def w317 : CWord := (.mul w294 w316)
private def w318 : CWord := (.mul w293 w317)
private def w319 : CWord := (.mul w292 w318)
private def w320 : CWord := (.mul w291 w319)
private def w321 : CWord := (.mul w290 w320)
private def w322 : CWord := (.mul w289 w321)
private def w323 : CWord := (.mul w288 w322)
private def w324 : CWord := (.mul w287 w323)
private def w325 : CWord := (.mul w286 w324)
private def w326 : CWord := (.mul w285 w325)
private def w327 : CWord := (.mul w284 w326)
private def w328 : CWord := (.mul w283 w327)
private def w329 : CWord := (.mul w280 w328)
private def w330 : CWord := (.mul w278 w329)
private def w331 : CWord := (.mul w276 w330)
private def w332 : CWord := (.mul w273 w331)
private def w333 : CWord := (.mul w269 w332)
private def w334 : CWord := (.mul w266 w333)
private def w335 : CWord := (.mul w262 w334)
private def w336 : CWord := (.mul w261 w335)
private def w337 : CWord := (.mul w260 w336)
private def w338 : CWord := (.mul w259 w337)
private def w339 : CWord := (.mul w258 w338)
private def w340 : CWord := (.mul w257 w339)
private def w341 : CWord := (.mul w255 w340)
private def w342 : CWord := (.mul w254 w341)
private def w343 : CWord := (.mul w253 w342)
private def w344 : CWord := (.mul w251 w343)
private def w345 : CWord := (.mul w249 w344)
private def w346 : CWord := (.mul w248 w345)
private def w347 : CWord := (.mul w247 w346)
private def w348 : CWord := (.mul w246 w347)
private def w349 : CWord := (.mul w243 w348)
private def w350 : CWord := (.mul w242 w349)
private def w351 : CWord := (.mul w240 w350)
private def w352 : CWord := (.mul w238 w351)
private def w353 : CWord := (.mul w237 w352)
private def w354 : CWord := (.mul w235 w353)
private def w355 : CWord := (.mul w71 w228)
private def w356 : CWord := (.mul w70 w355)
private def w357 : CWord := (.mul w309 w356)
private def w358 : CWord := (.comm w0 w230)
private def w359 : CWord := (.comm w24 w230)
private def w360 : CWord := (.mul w27 w28)
private def w361 : CWord := (.comm w360 w0)
private def w362 : CWord := (.sq w361)
private def w363 : CWord := (.sq w362)
private def w364 : CWord := (.comm w361 w0)
private def w365 : CWord := (.sq w364)
private def w366 : CWord := (.comm w360 w7)
private def w367 : CWord := (.comm w366 w0)
private def w368 : CWord := (.sq w367)
private def w369 : CWord := (.comm w361 w7)
private def w370 : CWord := (.sq w369)
private def w371 : CWord := (.comm w367 w0)
private def w372 : CWord := (.comm w364 w7)

private def consequenceTrace0 : Deriv :=
  (.trans
    (.sq
      (.sq
        (.comm
          (.rel)
          (.refl w0)
        )
      )
    )
    (.deep w4)
  )

private theorem consequenceTrace0_checked :
    consequenceTrace0.check = true := by decide

private theorem consequenceTrace0_sound :
    eval dmModel.val consequenceTrace0.lhs =
      eval dmModel.val consequenceTrace0.rhs :=
  Deriv.sound dmModel consequenceTrace0 consequenceTrace0_checked

private def consequenceTrace1 : Deriv :=
  (.trans
    (.sq
      (.comm
        (.comm
          (.rel)
          (.refl w0)
        )
        (.refl w0)
      )
    )
    (.deep w6)
  )

private theorem consequenceTrace1_checked :
    consequenceTrace1.check = true := by decide

private theorem consequenceTrace1_sound :
    eval dmModel.val consequenceTrace1.lhs =
      eval dmModel.val consequenceTrace1.rhs :=
  Deriv.sound dmModel consequenceTrace1 consequenceTrace1_checked

private def consequenceTrace2 : Deriv :=
  (.trans
    (.sq
      (.comm
        (.comm
          (.rel)
          (.refl w7)
        )
        (.refl w0)
      )
    )
    (.deep w10)
  )

private theorem consequenceTrace2_checked :
    consequenceTrace2.check = true := by decide

private theorem consequenceTrace2_sound :
    eval dmModel.val consequenceTrace2.lhs =
      eval dmModel.val consequenceTrace2.rhs :=
  Deriv.sound dmModel consequenceTrace2 consequenceTrace2_checked

private def consequenceTrace3 : Deriv :=
  (.trans
    (.sq
      (.comm
        (.comm
          (.rel)
          (.refl w0)
        )
        (.refl w7)
      )
    )
    (.deep w12)
  )

private theorem consequenceTrace3_checked :
    consequenceTrace3.check = true := by decide

private theorem consequenceTrace3_sound :
    eval dmModel.val consequenceTrace3.lhs =
      eval dmModel.val consequenceTrace3.rhs :=
  Deriv.sound dmModel consequenceTrace3 consequenceTrace3_checked

private def consequenceTrace4 : Deriv :=
  (.trans
    (.comm
      (.comm
        (.comm
          (.rel)
          (.refl w7)
        )
        (.refl w0)
      )
      (.refl w0)
    )
    (.deep w13)
  )

private theorem consequenceTrace4_checked :
    consequenceTrace4.check = true := by decide

private theorem consequenceTrace4_sound :
    eval dmModel.val consequenceTrace4.lhs =
      eval dmModel.val consequenceTrace4.rhs :=
  Deriv.sound dmModel consequenceTrace4 consequenceTrace4_checked

private def consequenceTrace5 : Deriv :=
  (.trans
    (.comm
      (.comm
        (.comm
          (.rel)
          (.refl w0)
        )
        (.refl w0)
      )
      (.refl w7)
    )
    (.deep w14)
  )

private theorem consequenceTrace5_checked :
    consequenceTrace5.check = true := by decide

private theorem consequenceTrace5_sound :
    eval dmModel.val consequenceTrace5.lhs =
      eval dmModel.val consequenceTrace5.rhs :=
  Deriv.sound dmModel consequenceTrace5 consequenceTrace5_checked

private def expandTrace0 : Deriv :=
  (.mul
    (.trans
      (.trans
        (.sq
          (.trans
            (.trans
              (.sq
                (.trans
                  (.comm_mul_left w27 w28 w0)
                  (.mul
                    (.mul
                      (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                      )
                      (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.comm_mul_left w35 w36 w28)
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w28)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w28)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.deep w38)
                        )
                        (.mul_one w37)
                        )
                        (.deep w39)
                        )
                        (.mul_one w37)
                        )
                        )
                        (.deep w41)
                        )
                        (.mul_one w37)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        )
                        )
                        (.deep w43)
                        )
                        (.mul_one w45)
                        )
                        (.deep w46)
                        )
                        (.mul_one w45)
                        )
                      )
                    )
                    (.comm
                      (.comm
                        (.refl w24)
                        (.refl w7)
                      )
                      (.refl w0)
                    )
                  )
                )
              )
              (.sq_mul w48 w49)
            )
            (.trans
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.trans
                        (.sq_mul w47 w45)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.sq_mul w35 w36)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.trans
                        (.sq_mul w33 w34)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.trans
                        (.sq_mul w31 w32)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.sq
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        )
                        (.deep w50)
                        )
                        (.mul_one w51)
                        )
                        (.deep w52)
                        )
                        (.mul_one w51)
                        )
                        (.deep w53)
                        )
                        (.mul_one w51)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w54)
                        )
                        (.mul_one w56)
                        )
                        (.deep w57)
                        )
                        (.mul_one w56)
                        )
                        )
                        (.sq
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w58)
                        )
                        (.mul_one w60)
                        )
                        (.deep w61)
                        )
                        (.mul_one w60)
                        )
                        )
                        (.deep w62)
                        )
                        (.mul_one w60)
                        )
                        (.deep w63)
                        )
                        (.mul_one w60)
                        )
                        (.deep w64)
                        )
                        (.mul_one w60)
                        )
                      )
                      (.sq
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                      )
                    )
                    (.deep w65)
                  )
                  (.mul_one w67)
                )
                (.deep w68)
              )
              (.mul_one w67)
            )
          )
        )
        (.sq_mul w60 w66)
      )
      (.trans
        (.mul
          (.trans
            (.mul
              (.mul
                (.trans
                  (.sq_mul w56 w59)
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.sq_mul w51 w55)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.sq
                        (.sq
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.sq
                        (.sq
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        )
                        (.deep w69)
                        )
                        (.mul_one w72)
                        )
                        (.deep w73)
                        )
                        (.mul_one w72)
                        )
                        )
                        (.deep w74)
                        )
                        (.mul_one w72)
                        )
                        (.deep w75)
                        )
                        (.mul_one w72)
                      )
                      (.deep w76)
                    )
                    (.mul_one w72)
                  )
                )
                (.sq
                  (.sq
                    (.comm
                      (.comm
                        (.refl w24)
                        (.refl w7)
                      )
                      (.refl w0)
                    )
                  )
                )
              )
              (.deep w77)
            )
            (.mul_one w79)
          )
          (.deep w80)
        )
        (.mul_one w79)
      )
    )
    (.mul
      (.trans
        (.trans
          (.sq
            (.trans
              (.trans
                (.comm
                  (.trans
                    (.comm_mul_left w27 w28 w0)
                    (.mul
                      (.mul
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.comm_mul_left w35 w36 w28)
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w28)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w28)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.deep w38)
                        )
                        (.mul_one w37)
                        )
                        (.deep w39)
                        )
                        (.mul_one w37)
                        )
                        )
                        (.deep w41)
                        )
                        (.mul_one w37)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        )
                        )
                        (.deep w43)
                        )
                        (.mul_one w45)
                        )
                        (.deep w46)
                        )
                        (.mul_one w45)
                        )
                        )
                      )
                      (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                      )
                    )
                  )
                  (.refl w0)
                )
                (.comm_mul_left w48 w49 w0)
              )
              (.mul
                (.trans
                  (.mul
                    (.trans
                      (.comm_mul_left w47 w45 w0)
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w35 w36 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.deep w82)
                        )
                        (.mul_one w81)
                        )
                        (.deep w83)
                        )
                        (.mul_one w81)
                        )
                        )
                        (.deep w85)
                        )
                        (.mul_one w81)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w87)
                        )
                        (.mul_one w89)
                        )
                        (.comm
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w91)
                        )
                        (.mul_one w93)
                        )
                        (.deep w94)
                        )
                        (.mul_one w93)
                      )
                    )
                    (.deep w96)
                  )
                  (.mul_one w93)
                )
                (.comm
                  (.comm
                    (.comm
                      (.refl w24)
                      (.refl w7)
                    )
                    (.refl w0)
                  )
                  (.refl w0)
                )
              )
            )
          )
          (.sq_mul w93 w97)
        )
        (.trans
          (.mul
            (.trans
              (.mul
                (.mul
                  (.trans
                    (.sq_mul w89 w92)
                    (.trans
                      (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.sq_mul w81 w88)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.sq
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w98)
                        )
                        (.mul_one w101)
                        )
                        (.deep w102)
                        )
                        (.mul_one w101)
                        )
                        )
                        (.deep w103)
                        )
                        (.mul_one w101)
                        )
                        (.deep w104)
                        )
                        (.mul_one w101)
                        )
                        (.deep w105)
                      )
                      (.mul_one w101)
                    )
                  )
                  (.sq
                    (.comm
                      (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                      )
                      (.refl w0)
                    )
                  )
                )
                (.deep w106)
              )
              (.mul_one w108)
            )
            (.deep w109)
          )
          (.mul_one w108)
        )
      )
      (.mul
        (.trans
          (.trans
            (.sq
              (.trans
                (.trans
                  (.comm
                    (.trans
                      (.comm_mul_left w27 w28 w7)
                      (.mul
                        (.mul
                        (.trans
                        (.comm_mul_left w23 w26 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w7)
                        (.deep w111)
                        )
                        (.mul_one w116)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_left w23 w26 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w7)
                        (.deep w111)
                        )
                        (.mul_one w116)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.comm_mul_left w116 w117 w28)
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w114 w115 w28)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w112 w113 w28)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w7)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.deep w119)
                        )
                        (.mul_one w118)
                        )
                        (.deep w120)
                        )
                        (.mul_one w118)
                        )
                        )
                        (.deep w122)
                        )
                        (.mul_one w118)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        )
                        )
                        (.deep w124)
                        )
                        (.mul_one w126)
                        )
                        (.deep w127)
                        )
                        (.mul_one w126)
                        )
                        )
                        )
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w7)
                        )
                      )
                    )
                    (.refl w0)
                  )
                  (.comm_mul_left w129 w130 w0)
                )
                (.mul
                  (.trans
                    (.mul
                      (.trans
                        (.comm_mul_left w128 w126 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w116 w117 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w114 w115 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w112 w113 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        (.deep w132)
                        )
                        (.mul_one w131)
                        )
                        (.deep w133)
                        )
                        (.mul_one w131)
                        )
                        )
                        (.deep w135)
                        )
                        (.mul_one w131)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w137)
                        )
                        (.mul_one w139)
                        )
                        (.comm
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w141)
                        )
                        (.mul_one w143)
                        )
                        (.deep w144)
                        )
                        (.mul_one w143)
                        )
                      )
                      (.deep w146)
                    )
                    (.mul_one w143)
                  )
                  (.comm
                    (.comm
                      (.comm
                        (.refl w24)
                        (.refl w7)
                      )
                      (.refl w7)
                    )
                    (.refl w0)
                  )
                )
              )
            )
            (.sq_mul w143 w147)
          )
          (.trans
            (.mul
              (.trans
                (.mul
                  (.mul
                    (.trans
                      (.sq_mul w139 w142)
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.sq_mul w131 w138)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.sq
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w148)
                        )
                        (.mul_one w151)
                        )
                        (.deep w152)
                        )
                        (.mul_one w151)
                        )
                        )
                        (.deep w153)
                        )
                        (.mul_one w151)
                        )
                        (.deep w154)
                        )
                        (.mul_one w151)
                        )
                        (.deep w155)
                        )
                        (.mul_one w151)
                      )
                    )
                    (.sq
                      (.comm
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                      )
                    )
                  )
                  (.deep w156)
                )
                (.mul_one w158)
              )
              (.deep w159)
            )
            (.mul_one w158)
          )
        )
        (.mul
          (.trans
            (.trans
              (.sq
                (.trans
                  (.trans
                    (.comm
                      (.trans
                        (.comm_mul_left w27 w28 w0)
                        (.mul
                        (.mul
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.comm_mul_left w35 w36 w28)
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w28)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w28)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.deep w38)
                        )
                        (.mul_one w37)
                        )
                        (.deep w39)
                        )
                        (.mul_one w37)
                        )
                        )
                        (.deep w41)
                        )
                        (.mul_one w37)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        )
                        )
                        (.deep w43)
                        )
                        (.mul_one w45)
                        )
                        (.deep w46)
                        )
                        (.mul_one w45)
                        )
                        )
                        )
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                      )
                      (.refl w7)
                    )
                    (.comm_mul_left w48 w49 w7)
                  )
                  (.mul
                    (.trans
                      (.mul
                        (.trans
                        (.comm_mul_left w47 w45 w7)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w35 w36 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w7)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.deep w161)
                        )
                        (.mul_one w160)
                        )
                        (.deep w162)
                        )
                        (.mul_one w160)
                        )
                        )
                        (.deep w164)
                        )
                        (.mul_one w160)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.deep w166)
                        )
                        (.mul_one w168)
                        )
                        (.comm
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.deep w170)
                        )
                        (.mul_one w172)
                        )
                        (.deep w173)
                        )
                        (.mul_one w172)
                        )
                        )
                        (.deep w175)
                      )
                      (.mul_one w172)
                    )
                    (.comm
                      (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                      )
                      (.refl w7)
                    )
                  )
                )
              )
              (.sq_mul w172 w176)
            )
            (.trans
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.trans
                        (.sq_mul w168 w171)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.sq_mul w160 w167)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.sq
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.deep w177)
                        )
                        (.mul_one w180)
                        )
                        (.deep w181)
                        )
                        (.mul_one w180)
                        )
                        )
                        (.deep w182)
                        )
                        (.mul_one w180)
                        )
                        (.deep w183)
                        )
                        (.mul_one w180)
                        )
                        (.deep w184)
                        )
                        (.mul_one w180)
                        )
                      )
                      (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                      )
                    )
                    (.deep w185)
                  )
                  (.mul_one w187)
                )
                (.deep w188)
              )
              (.mul_one w187)
            )
          )
          (.mul
            (.trans
              (.trans
                (.comm
                  (.trans
                    (.trans
                      (.comm
                        (.trans
                        (.comm_mul_left w27 w28 w7)
                        (.mul
                        (.mul
                        (.trans
                        (.comm_mul_left w23 w26 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w7)
                        (.deep w111)
                        )
                        (.mul_one w116)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_left w23 w26 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w7)
                        (.deep w111)
                        )
                        (.mul_one w116)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.comm_mul_left w116 w117 w28)
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w114 w115 w28)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w112 w113 w28)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w7)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.deep w119)
                        )
                        (.mul_one w118)
                        )
                        (.deep w120)
                        )
                        (.mul_one w118)
                        )
                        )
                        (.deep w122)
                        )
                        (.mul_one w118)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        )
                        )
                        (.deep w124)
                        )
                        (.mul_one w126)
                        )
                        (.deep w127)
                        )
                        (.mul_one w126)
                        )
                        )
                        )
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.refl w0)
                      )
                      (.comm_mul_left w129 w130 w0)
                    )
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w128 w126 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w116 w117 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w114 w115 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w112 w113 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        (.deep w132)
                        )
                        (.mul_one w131)
                        )
                        (.deep w133)
                        )
                        (.mul_one w131)
                        )
                        )
                        (.deep w135)
                        )
                        (.mul_one w131)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w137)
                        )
                        (.mul_one w139)
                        )
                        (.comm
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w141)
                        )
                        (.mul_one w143)
                        )
                        (.deep w144)
                        )
                        (.mul_one w143)
                        )
                        )
                        (.deep w146)
                        )
                        (.mul_one w143)
                      )
                      (.comm
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                      )
                    )
                  )
                  (.refl w0)
                )
                (.comm_mul_left w143 w147 w0)
              )
              (.mul
                (.trans
                  (.mul
                    (.trans
                      (.comm_mul_left w139 w142 w0)
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w131 w138 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.deep w190)
                        )
                        (.mul_one w189)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w192)
                        )
                        (.mul_one w194)
                        )
                        (.deep w195)
                        )
                        (.mul_one w194)
                      )
                    )
                    (.deep w197)
                  )
                  (.mul_one w194)
                )
                (.comm
                  (.comm
                    (.comm
                      (.comm
                        (.refl w24)
                        (.refl w7)
                      )
                      (.refl w7)
                    )
                    (.refl w0)
                  )
                  (.refl w0)
                )
              )
            )
            (.trans
              (.trans
                (.comm
                  (.trans
                    (.trans
                      (.comm
                        (.trans
                        (.comm_mul_left w27 w28 w0)
                        (.mul
                        (.mul
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_left w23 w26 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.comm_mul_left w21 w22 w0)
                        (.deep w30)
                        )
                        (.mul_one w35)
                        )
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.comm_mul_left w35 w36 w28)
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w28)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w28)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        (.deep w38)
                        )
                        (.mul_one w37)
                        )
                        (.deep w39)
                        )
                        (.mul_one w37)
                        )
                        )
                        (.deep w41)
                        )
                        (.mul_one w37)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        )
                        )
                        )
                        (.deep w43)
                        )
                        (.mul_one w45)
                        )
                        (.deep w46)
                        )
                        (.mul_one w45)
                        )
                        )
                        )
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.refl w0)
                      )
                      (.comm_mul_left w48 w49 w0)
                    )
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w47 w45 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w35 w36 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w33 w34 w0)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w31 w32 w0)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.deep w82)
                        )
                        (.mul_one w81)
                        )
                        (.deep w83)
                        )
                        (.mul_one w81)
                        )
                        )
                        (.deep w85)
                        )
                        (.mul_one w81)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w87)
                        )
                        (.mul_one w89)
                        )
                        (.comm
                        (.comm
                        (.sq
                        (.sq
                        (.refl w24)
                        )
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        )
                        )
                        (.deep w91)
                        )
                        (.mul_one w93)
                        )
                        (.deep w94)
                        )
                        (.mul_one w93)
                        )
                        )
                        (.deep w96)
                        )
                        (.mul_one w93)
                      )
                      (.comm
                        (.comm
                        (.comm
                        (.refl w24)
                        (.refl w7)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                      )
                    )
                  )
                  (.refl w7)
                )
                (.comm_mul_left w93 w97 w7)
              )
              (.mul
                (.trans
                  (.mul
                    (.trans
                      (.comm_mul_left w89 w92 w7)
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w81 w88 w7)
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.comm
                        (.sq
                        (.refl w20)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        (.deep w199)
                        )
                        (.mul_one w198)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w20)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w7)
                        )
                        )
                        )
                        (.deep w201)
                        )
                        (.mul_one w203)
                        )
                        (.deep w204)
                        )
                        (.mul_one w203)
                      )
                    )
                    (.deep w206)
                  )
                  (.mul_one w203)
                )
                (.comm
                  (.comm
                    (.comm
                      (.comm
                        (.refl w24)
                        (.refl w7)
                      )
                      (.refl w0)
                    )
                    (.refl w0)
                  )
                  (.refl w7)
                )
              )
            )
          )
        )
      )
    )
  )

private theorem expandTrace0_checked : expandTrace0.check = true := by decide

private theorem expandTrace0_sound :
    eval dmModel.val expandTrace0.lhs = eval dmModel.val expandTrace0.rhs :=
  Deriv.sound dmModel expandTrace0 expandTrace0_checked

private def expandTrace1 : Deriv :=
  (.mul
    (.trans
      (.mul
        (.mul
          (.refl w70)
          (.refl w71)
        )
        (.refl w78)
      )
      (.trans
        (.assoc w70 w71 w78)
        (.mul
          (.refl w70)
          (.refl w207)
        )
      )
    )
    (.trans
      (.mul
        (.trans
          (.mul
            (.mul
              (.refl w99)
              (.refl w100)
            )
            (.refl w107)
          )
          (.trans
            (.assoc w99 w100 w107)
            (.mul
              (.refl w99)
              (.refl w208)
            )
          )
        )
        (.trans
          (.mul
            (.trans
              (.mul
                (.mul
                  (.refl w149)
                  (.refl w150)
                )
                (.refl w157)
              )
              (.trans
                (.assoc w149 w150 w157)
                (.mul
                  (.refl w149)
                  (.refl w209)
                )
              )
            )
            (.trans
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.refl w178)
                      (.refl w179)
                    )
                    (.refl w186)
                  )
                  (.trans
                    (.assoc w178 w179 w186)
                    (.mul
                      (.refl w178)
                      (.refl w210)
                    )
                  )
                )
                (.trans
                  (.mul
                    (.trans
                      (.mul
                        (.mul
                        (.refl w189)
                        (.refl w193)
                        )
                        (.refl w211)
                      )
                      (.trans
                        (.assoc w189 w193 w211)
                        (.mul
                        (.refl w189)
                        (.refl w212)
                        )
                      )
                    )
                    (.trans
                      (.mul
                        (.mul
                        (.refl w198)
                        (.refl w202)
                        )
                        (.refl w213)
                      )
                      (.trans
                        (.assoc w198 w202 w213)
                        (.mul
                        (.refl w198)
                        (.refl w214)
                        )
                      )
                    )
                  )
                  (.trans
                    (.assoc w189 w212 w215)
                    (.mul
                      (.refl w189)
                      (.trans
                        (.assoc w193 w211 w215)
                        (.mul
                        (.refl w193)
                        (.refl w216)
                        )
                      )
                    )
                  )
                )
              )
              (.trans
                (.assoc w178 w210 w218)
                (.mul
                  (.refl w178)
                  (.trans
                    (.assoc w179 w186 w218)
                    (.mul
                      (.refl w179)
                      (.refl w219)
                    )
                  )
                )
              )
            )
          )
          (.trans
            (.assoc w149 w209 w221)
            (.mul
              (.refl w149)
              (.trans
                (.assoc w150 w157 w221)
                (.mul
                  (.refl w150)
                  (.refl w222)
                )
              )
            )
          )
        )
      )
      (.trans
        (.assoc w99 w208 w224)
        (.mul
          (.refl w99)
          (.trans
            (.assoc w100 w107 w224)
            (.mul
              (.refl w100)
              (.refl w225)
            )
          )
        )
      )
    )
  )

private theorem expandTrace1_checked : expandTrace1.check = true := by decide

private theorem expandTrace1_sound :
    eval dmModel.val expandTrace1.lhs = eval dmModel.val expandTrace1.rhs :=
  Deriv.sound dmModel expandTrace1 expandTrace1_checked

private def expandTrace2 : Deriv :=
  (.assoc w70 w207 w227)

private theorem expandTrace2_checked : expandTrace2.check = true := by decide

private theorem expandTrace2_sound :
    eval dmModel.val expandTrace2.lhs = eval dmModel.val expandTrace2.rhs :=
  Deriv.sound dmModel expandTrace2 expandTrace2_checked

private def expandTrace3 : Deriv :=
  (.mul
    (.refl w70)
    (.trans
      (.assoc w71 w78 w227)
      (.mul
        (.refl w71)
        (.refl w228)
      )
    )
  )

private theorem expandTrace3_checked : expandTrace3.check = true := by decide

private theorem expandTrace3_sound :
    eval dmModel.val expandTrace3.lhs = eval dmModel.val expandTrace3.rhs :=
  Deriv.sound dmModel expandTrace3 expandTrace3_checked

private theorem expandBlock0_sound :
    eval dmModel.val expandTrace0.lhs =
      eval dmModel.val expandTrace3.rhs :=
  calc
    _ = eval dmModel.val expandTrace0.rhs := expandTrace0_sound
    _ = eval dmModel.val expandTrace1.rhs := expandTrace1_sound
    _ = eval dmModel.val expandTrace2.rhs := expandTrace2_sound
    _ = eval dmModel.val expandTrace3.rhs := expandTrace3_sound

private def relationProductTrace : Deriv :=
  (.trans
    (.mul
      (.trans
        (.sq
          (.sq
            (.comm
              (.rel)
              (.refl w0)
            )
          )
        )
        (.deep w4)
      )
      (.mul
        (.trans
          (.sq
            (.comm
              (.comm
                (.rel)
                (.refl w0)
              )
              (.refl w0)
            )
          )
          (.deep w6)
        )
        (.mul
          (.trans
            (.sq
              (.comm
                (.comm
                  (.rel)
                  (.refl w7)
                )
                (.refl w0)
              )
            )
            (.deep w10)
          )
          (.mul
            (.trans
              (.sq
                (.comm
                  (.comm
                    (.rel)
                    (.refl w0)
                  )
                  (.refl w7)
                )
              )
              (.deep w12)
            )
            (.mul
              (.trans
                (.comm
                  (.comm
                    (.comm
                      (.rel)
                      (.refl w7)
                    )
                    (.refl w0)
                  )
                  (.refl w0)
                )
                (.deep w13)
              )
              (.trans
                (.comm
                  (.comm
                    (.comm
                      (.rel)
                      (.refl w0)
                    )
                    (.refl w0)
                  )
                  (.refl w7)
                )
                (.deep w14)
              )
            )
          )
        )
      )
    )
    (.deep w19)
  )

private theorem relationProductTrace_checked : relationProductTrace.check = true := by decide

private theorem relationProductTrace_sound :
    eval dmModel.val relationProductTrace.lhs = eval dmModel.val relationProductTrace.rhs :=
  Deriv.sound dmModel relationProductTrace relationProductTrace_checked

private def joinTrace : Deriv :=
  (.trans
    (.assoc w232 w354 w356)
    (.mul
      (.refl w232)
      (.trans
        (.assoc w235 w353 w356)
        (.mul
          (.refl w235)
          (.trans
            (.assoc w237 w352 w356)
            (.mul
              (.refl w237)
              (.trans
                (.assoc w238 w351 w356)
                (.mul
                  (.refl w238)
                  (.trans
                    (.assoc w240 w350 w356)
                    (.mul
                      (.refl w240)
                      (.trans
                        (.assoc w242 w349 w356)
                        (.mul
                        (.refl w242)
                        (.trans
                        (.assoc w243 w348 w356)
                        (.mul
                        (.refl w243)
                        (.trans
                        (.assoc w246 w347 w356)
                        (.mul
                        (.refl w246)
                        (.trans
                        (.assoc w247 w346 w356)
                        (.mul
                        (.refl w247)
                        (.trans
                        (.assoc w248 w345 w356)
                        (.mul
                        (.refl w248)
                        (.trans
                        (.assoc w249 w344 w356)
                        (.mul
                        (.refl w249)
                        (.trans
                        (.assoc w251 w343 w356)
                        (.mul
                        (.refl w251)
                        (.trans
                        (.assoc w253 w342 w356)
                        (.mul
                        (.refl w253)
                        (.trans
                        (.assoc w254 w341 w356)
                        (.mul
                        (.refl w254)
                        (.trans
                        (.assoc w255 w340 w356)
                        (.mul
                        (.refl w255)
                        (.trans
                        (.assoc w257 w339 w356)
                        (.mul
                        (.refl w257)
                        (.trans
                        (.assoc w258 w338 w356)
                        (.mul
                        (.refl w258)
                        (.trans
                        (.assoc w259 w337 w356)
                        (.mul
                        (.refl w259)
                        (.trans
                        (.assoc w260 w336 w356)
                        (.mul
                        (.refl w260)
                        (.trans
                        (.assoc w261 w335 w356)
                        (.mul
                        (.refl w261)
                        (.trans
                        (.assoc w262 w334 w356)
                        (.mul
                        (.refl w262)
                        (.trans
                        (.assoc w266 w333 w356)
                        (.mul
                        (.refl w266)
                        (.trans
                        (.assoc w269 w332 w356)
                        (.mul
                        (.refl w269)
                        (.trans
                        (.assoc w273 w331 w356)
                        (.mul
                        (.refl w273)
                        (.trans
                        (.assoc w276 w330 w356)
                        (.mul
                        (.refl w276)
                        (.trans
                        (.assoc w278 w329 w356)
                        (.mul
                        (.refl w278)
                        (.trans
                        (.assoc w280 w328 w356)
                        (.mul
                        (.refl w280)
                        (.trans
                        (.assoc w283 w327 w356)
                        (.mul
                        (.refl w283)
                        (.trans
                        (.assoc w284 w326 w356)
                        (.mul
                        (.refl w284)
                        (.trans
                        (.assoc w285 w325 w356)
                        (.mul
                        (.refl w285)
                        (.trans
                        (.assoc w286 w324 w356)
                        (.mul
                        (.refl w286)
                        (.trans
                        (.assoc w287 w323 w356)
                        (.mul
                        (.refl w287)
                        (.trans
                        (.assoc w288 w322 w356)
                        (.mul
                        (.refl w288)
                        (.trans
                        (.assoc w289 w321 w356)
                        (.mul
                        (.refl w289)
                        (.trans
                        (.assoc w290 w320 w356)
                        (.mul
                        (.refl w290)
                        (.trans
                        (.assoc w291 w319 w356)
                        (.mul
                        (.refl w291)
                        (.trans
                        (.assoc w292 w318 w356)
                        (.mul
                        (.refl w292)
                        (.trans
                        (.assoc w293 w317 w356)
                        (.mul
                        (.refl w293)
                        (.trans
                        (.assoc w294 w316 w356)
                        (.mul
                        (.refl w294)
                        (.trans
                        (.assoc w296 w315 w356)
                        (.mul
                        (.refl w296)
                        (.trans
                        (.assoc w297 w314 w356)
                        (.mul
                        (.refl w297)
                        (.trans
                        (.assoc w298 w313 w356)
                        (.mul
                        (.refl w298)
                        (.trans
                        (.assoc w300 w312 w356)
                        (.mul
                        (.refl w300)
                        (.trans
                        (.assoc w303 w311 w356)
                        (.mul
                        (.refl w303)
                        (.trans
                        (.assoc w305 w310 w356)
                        (.mul
                        (.refl w305)
                        (.trans
                        (.assoc w306 w309 w356)
                        (.mul
                        (.refl w306)
                        (.refl w357)
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
    )
  )

private theorem joinTrace_checked : joinTrace.check = true := by decide

private theorem joinTrace_sound :
    eval dmModel.val joinTrace.lhs = eval dmModel.val joinTrace.rhs :=
  Deriv.sound dmModel joinTrace joinTrace_checked

def consequenceTraces : List Deriv :=
  [ consequenceTrace0, consequenceTrace1, consequenceTrace2, consequenceTrace3, consequenceTrace4,
    consequenceTrace5 ]

def relSqSqB : CWord := (.sq w362)
def relSqBB : CWord := (.sq w364)
def relSqDB : CWord := (.sq w367)
def relSqBD : CWord := (.sq w369)
def relDBB : CWord := (.comm w367 w0)
def relBBD : CWord := (.comm w364 w7)

def relationConsequences : List CWord :=
  [ relSqSqB, relSqBB, relSqDB, relSqBD, relDBB,
    relBBD ]

def relationProduct : CWord :=
  MpcC6WeightedTracePrefix.rightProduct relationConsequences

/-- The six relation-support factors, exposed without the generated collector names. -/
theorem eval_relationProduct_shape {Q : Type*} [Group Q] (val : Gen4 → Q) :
    let R := eval val mRel
    let K := commP R (val .B)
    let L := commP R (val .D)
    eval val relationProduct =
      K ^ 4 * commP K (val .B) ^ 2 * commP L (val .B) ^ 2 *
        commP K (val .D) ^ 2 * commP (commP L (val .B)) (val .B) *
        commP (commP K (val .B)) (val .D) := by
  simp only [relationProduct, relationConsequences, relSqSqB, relSqBB,
    relSqDB, relSqBD, relDBB, relBBD,
    MpcC6WeightedTracePrefix.rightProduct, eval, w362, w364, w367,
    w369, w361, w366, w360, w27, w28, w23, w26, w25, w21, w22,
    w20, w24, w0, w7, mRel]
  norm_num [← pow_mul]
  group

def expandedRelationFactors : List CWord :=
  [ w70, w71, w78, w99, w100,
    w107, w149, w150, w157, w178,
    w179, w186, w189, w193, w211,
    w198, w202, w213 ]

def expandedRelationProduct : CWord :=
  MpcC6WeightedTracePrefix.rightProduct expandedRelationFactors

private def lowFactors : List CWord :=
  [ w232, w235, w237, w238, w240,
    w242, w243, w246, w247, w248,
    w249, w251, w253, w254, w255,
    w257, w258, w259, w260, w261,
    w262, w266, w269, w273, w276,
    w278, w280, w283, w284, w285,
    w286, w287, w288, w289, w290,
    w291, w292, w293, w294, w296,
    w297, w298, w300, w303, w305,
    w306, w309 ]

def endpointFactors : List CWord :=
  [ w232, w235, w237, w238, w240,
    w242, w243, w246, w247, w248,
    w249, w251, w253, w254, w255,
    w257, w258, w259, w260, w261,
    w262, w266, w269, w273, w276,
    w278, w280, w283, w284, w285,
    w286, w287, w288, w289, w290,
    w291, w292, w293, w294, w296,
    w297, w298, w300, w303, w305,
    w306, w309, w70, w71, w78,
    w99, w100, w107, w149, w150,
    w157, w178, w179, w186, w189,
    w193, w211, w198, w202, w213 ]

def endpoint : CWord :=
  MpcC6WeightedTracePrefix.rightProduct endpointFactors

theorem consequenceTraces_all_checked :
    consequenceTraces.all Deriv.check = true := by decide

theorem relationConsequences_length : relationConsequences.length = 6 := by decide

theorem relationConsequences_all_depth_five :
    relationConsequences.all (fun w => decide (w.depth = 5)) = true := by decide

theorem eval_relSqSqB_eq_one : eval dmModel.val relSqSqB = 1 := by
  rw [← show consequenceTrace0.lhs = relSqSqB by decide]
  simpa only [show consequenceTrace0.rhs = (.one : CWord) by decide, eval] using
    consequenceTrace0_sound

theorem eval_relSqBB_eq_one : eval dmModel.val relSqBB = 1 := by
  rw [← show consequenceTrace1.lhs = relSqBB by decide]
  simpa only [show consequenceTrace1.rhs = (.one : CWord) by decide, eval] using
    consequenceTrace1_sound

theorem eval_relSqDB_eq_one : eval dmModel.val relSqDB = 1 := by
  rw [← show consequenceTrace2.lhs = relSqDB by decide]
  simpa only [show consequenceTrace2.rhs = (.one : CWord) by decide, eval] using
    consequenceTrace2_sound

theorem eval_relSqBD_eq_one : eval dmModel.val relSqBD = 1 := by
  rw [← show consequenceTrace3.lhs = relSqBD by decide]
  simpa only [show consequenceTrace3.rhs = (.one : CWord) by decide, eval] using
    consequenceTrace3_sound

theorem eval_relDBB_eq_one : eval dmModel.val relDBB = 1 := by
  rw [← show consequenceTrace4.lhs = relDBB by decide]
  simpa only [show consequenceTrace4.rhs = (.one : CWord) by decide, eval] using
    consequenceTrace4_sound

theorem eval_relBBD_eq_one : eval dmModel.val relBBD = 1 := by
  rw [← show consequenceTrace5.lhs = relBBD by decide]
  simpa only [show consequenceTrace5.rhs = (.one : CWord) by decide, eval] using
    consequenceTrace5_sound

theorem expandedRelationFactors_length : expandedRelationFactors.length = 18 := by decide

theorem expandedRelationFactors_all_depth_five :
    expandedRelationFactors.all (fun w => decide (w.depth = 5)) = true := by decide

theorem endpointFactors_length : endpointFactors.length = 65 := by decide

theorem endpointFactors_all_depth_five :
    endpointFactors.all (fun w => decide (w.depth = 5)) = true := by decide

private theorem lowFactors_eq : lowFactors = MpcC6WeightedTraceLow.endpointFactors := by decide

private theorem relationProductTrace_lhs : relationProductTrace.lhs = relationProduct := by decide

private theorem relationProductTrace_rhs : relationProductTrace.rhs = .one := by decide

theorem eval_relationProduct_eq_one : eval dmModel.val relationProduct = 1 := by
  rw [← relationProductTrace_lhs, ← show eval dmModel.val (.one : CWord) = 1 by rfl]
  rw [← relationProductTrace_rhs]
  exact relationProductTrace_sound

private theorem expandTrace_lhs : expandTrace0.lhs = relationProduct := by decide

private theorem expandTrace_rhs : expandTrace3.rhs = expandedRelationProduct := by decide

private theorem expandedRelation_sound :
    eval dmModel.val relationProduct = eval dmModel.val expandedRelationProduct := by
  rw [← expandTrace_lhs, ← expandTrace_rhs]
  calc
    _ = eval dmModel.val expandTrace3.rhs := expandBlock0_sound

theorem eval_expandedRelationProduct_eq_one :
    eval dmModel.val expandedRelationProduct = 1 :=
  expandedRelation_sound.symm.trans eval_relationProduct_eq_one

private theorem joinTrace_lhs :
    joinTrace.lhs = .mul MpcC6WeightedTraceLow.endpoint expandedRelationProduct := by
  rw [MpcC6WeightedTraceLow.endpoint_eq_prefix_rightProduct]
  rw [← lowFactors_eq]
  decide

private theorem joinTrace_rhs : joinTrace.rhs = endpoint := by decide

private theorem eval_join :
    eval dmModel.val (.mul MpcC6WeightedTraceLow.endpoint expandedRelationProduct) =
      eval dmModel.val endpoint := by
  rw [← joinTrace_lhs, ← joinTrace_rhs]
  exact joinTrace_sound

theorem eval_certificateWord_eq_endpoint :
    eval dmModel.val MpcC6WeightedCertificate.Bridge.certificateWord =
      eval dmModel.val endpoint := by
  calc
    _ = eval dmModel.val MpcC6WeightedTraceLow.endpoint :=
      MpcC6WeightedTraceLow.eval_certificateWord_eq_endpoint
    _ = eval dmModel.val MpcC6WeightedTraceLow.endpoint * 1 :=
      (mul_one _).symm
    _ = eval dmModel.val MpcC6WeightedTraceLow.endpoint *
        eval dmModel.val expandedRelationProduct := by
      rw [eval_expandedRelationProduct_eq_one]
    _ = eval dmModel.val
        (.mul MpcC6WeightedTraceLow.endpoint expandedRelationProduct) := rfl
    _ = eval dmModel.val endpoint := eval_join

theorem certificateKill_of_jacobiEndpoint
    (hJacobi : eval dmModel.val endpoint = 1) :
    eval dmModel.val MpcC6WeightedCertificate.Bridge.certificateWord = 1 :=
  eval_certificateWord_eq_endpoint.trans hJacobi

private def expandChain : Deriv :=
  Deriv.chain [expandTrace0, expandTrace1, expandTrace2, expandTrace3]

private theorem expandChain_checked : expandChain.check = true := by decide

private theorem expandChain_noRel : expandChain.noRel = true := by decide

private theorem expandChain_lhs : expandChain.lhs = relationProduct := by decide

private theorem expandChain_rhs : expandChain.rhs = expandedRelationProduct := by decide

/-- Expanding the six relation consequences is itself relation-free. -/
theorem eval_relationProduct_eq_expanded_noRel
    {Q : Type*} [Group Q] (M : DeepModel Q) :
    eval M.val relationProduct = eval M.val expandedRelationProduct := by
  rw [← expandChain_lhs, ← expandChain_rhs]
  exact Deriv.soundNoRel M expandChain expandChain_checked expandChain_noRel

private theorem joinTrace_noRel : joinTrace.noRel = true := by decide

/-- Joining the low and relation-support blocks is relation-free. -/
theorem eval_low_mul_expanded_eq_endpoint_noRel
    {Q : Type*} [Group Q] (M : DeepModel Q) :
    eval M.val (.mul MpcC6WeightedTraceLow.endpoint expandedRelationProduct) =
      eval M.val endpoint := by
  rw [← joinTrace_lhs, ← joinTrace_rhs]
  exact Deriv.soundNoRel M joinTrace joinTrace_checked joinTrace_noRel

/-- Universal checked identity: the compact certificate times its six relation consequences
is the final Jacobi endpoint. -/
theorem eval_certificateWord_mul_relationProduct_eq_endpoint_noRel
    {Q : Type*} [Group Q] (M : DeepModel Q) :
    eval M.val MpcC6WeightedCertificate.Bridge.certificateWord *
        eval M.val relationProduct = eval M.val endpoint := by
  calc
    _ = eval M.val MpcC6WeightedTraceLow.endpoint *
        eval M.val relationProduct := by
      rw [MpcC6WeightedTraceLow.eval_certificateWord_eq_endpoint_noRel M]
    _ = eval M.val MpcC6WeightedTraceLow.endpoint *
        eval M.val expandedRelationProduct := by
      rw [eval_relationProduct_eq_expanded_noRel M]
    _ = eval M.val
        (.mul MpcC6WeightedTraceLow.endpoint expandedRelationProduct) := rfl
    _ = eval M.val endpoint := eval_low_mul_expanded_eq_endpoint_noRel M

#print axioms consequenceTraces_all_checked
#print axioms relationConsequences_all_depth_five
#print axioms eval_relSqSqB_eq_one
#print axioms eval_relSqBB_eq_one
#print axioms eval_relSqDB_eq_one
#print axioms eval_relSqBD_eq_one
#print axioms eval_relDBB_eq_one
#print axioms eval_relBBD_eq_one
#print axioms expandedRelationFactors_all_depth_five
#print axioms endpointFactors_all_depth_five
#print axioms eval_expandedRelationProduct_eq_one
#print axioms eval_certificateWord_eq_endpoint
#print axioms certificateKill_of_jacobiEndpoint
#print axioms eval_relationProduct_eq_expanded_noRel
#print axioms eval_low_mul_expanded_eq_endpoint_noRel
#print axioms eval_certificateWord_mul_relationProduct_eq_endpoint_noRel

end GQ2.Dyadic.Instances.MpcC6WeightedRelationSupport
