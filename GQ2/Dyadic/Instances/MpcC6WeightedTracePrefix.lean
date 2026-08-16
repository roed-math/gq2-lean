/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcC6WeightedCertificate

/-!
A checked collection prefix for the reflected class-six Mpc certificate.  The untrusted
generator emits only `CWord.Deriv` constructors; the kernel checks each bounded chunk and the
soundness theorem chains their evaluations.  The endpoint has 51 factors.  Its only depth-three
factors form the remaining restricted-square seam
`[D,B]^2 * [[D,B],B] * [B^2,D]`; this module does not claim that seam vanishes.
-/

namespace GQ2.Dyadic.Instances.MpcC6WeightedTracePrefix

open GQ2.Dyadic.Instances.MpcC6WeightedChecker
open GQ2.Dyadic.Instances.MpcC6WeightedChecker.CWord
open GQ2.Dyadic.Instances.MpcC6WeightedCertificate.Bridge

private def w0 : CWord := (.gen .D)
private def w1 : CWord := (.gen .B)
private def w2 : CWord := (.gen .A)
private def w3 : CWord := (.sq w1)
private def w4 : CWord := (.sq w3)
private def w5 : CWord := (.comm w4 w2)
private def w6 : CWord := (.inv w5)
private def w7 : CWord := (.inv w4)
private def w8 : CWord := (.comm w6 w7)
private def w9 : CWord := (.comm w2 w4)
private def w10 : CWord := (.comm w0 w1)
private def w11 : CWord := (.comm w10 w4)
private def w12 : CWord := (.inv w11)
private def w13 : CWord := (.comm w12 w7)
private def w14 : CWord := (.comm w4 w10)
private def w15 : CWord := (.comm w10 w2)
private def w16 : CWord := (.comm w15 w7)
private def w17 : CWord := (.comm w2 w10)
private def w18 : CWord := (.comm w17 w4)
private def w19 : CWord := (.mul w9 w17)
private def w20 : CWord := (.comm w10 w10)
private def w21 : CWord := (.comm w20 w4)
private def w22 : CWord := (.comm w4 w1)
private def w23 : CWord := (.inv w22)
private def w24 : CWord := (.comm w23 w7)
private def w25 : CWord := (.comm w1 w4)
private def w26 : CWord := (.comm w2 w1)
private def w27 : CWord := (.comm w26 w10)
private def w28 : CWord := (.comm w27 w4)
private def w29 : CWord := (.comm w26 w4)
private def w30 : CWord := (.mul w29 w27)
private def w31 : CWord := (.mul w10 w4)
private def w32 : CWord := (.comm w2 w31)
private def w33 : CWord := (.comm w32 w7)
private def w34 : CWord := (.comm w7 w4)
private def w35 : CWord := (.inv w14)
private def w36 : CWord := (.comm w35 w7)
private def w37 : CWord := (.comm w7 w10)
private def w38 : CWord := (.comm w37 w4)
private def w39 : CWord := (.comm w9 w10)
private def w40 : CWord := (.comm w39 w17)
private def w41 : CWord := (.mul w39 w40)
private def w42 : CWord := (.comm w17 w10)
private def w43 : CWord := (.inv w29)
private def w44 : CWord := (.comm w43 w7)
private def w45 : CWord := (.comm w4 w26)
private def w46 : CWord := (.comm w10 w1)
private def w47 : CWord := (.comm w46 w4)
private def w48 : CWord := (.comm w46 w10)
private def w49 : CWord := (.comm w48 w4)
private def w50 : CWord := (.comm w9 w26)
private def w51 : CWord := (.comm w50 w17)
private def w52 : CWord := (.mul w50 w51)
private def w53 : CWord := (.comm w17 w26)
private def w54 : CWord := (.gen .C)
private def w55 : CWord := (.comm w54 w3)
private def w56 : CWord := (.comm w55 w4)
private def w57 : CWord := (.sq w54)
private def w58 : CWord := (.comm w57 w4)
private def w59 : CWord := (.comm w55 w57)
private def w60 : CWord := (.mul w58 w59)
private def w61 : CWord := (.comm w3 w0)
private def w62 : CWord := (.comm w54 w4)
private def w63 : CWord := (.comm w62 w61)
private def w64 : CWord := (.comm w54 w61)
private def w65 : CWord := (.mul w64 w62)
private def w66 : CWord := (.comm w3 w4)
private def w67 : CWord := (.comm w66 w61)
private def w68 : CWord := (.comm w3 w61)
private def w69 : CWord := (.mul w68 w66)
private def w70 : CWord := (.comm w54 w0)
private def w71 : CWord := (.comm w70 w4)
private def w72 : CWord := (.comm w71 w61)
private def w73 : CWord := (.comm w70 w61)
private def w74 : CWord := (.mul w73 w71)
private def w75 : CWord := (.mul w4 w61)
private def w76 : CWord := (.comm w54 w75)
private def w77 : CWord := (.comm w76 w70)
private def w78 : CWord := (.comm w61 w70)
private def w79 : CWord := (.comm w3 w75)
private def w80 : CWord := (.comm w79 w54)
private def w81 : CWord := (.comm w61 w75)
private def w82 : CWord := (.sq w10)
private def w83 : CWord := (.mul w82 w15)
private def w84 : CWord := (.sq w4)
private def w85 : CWord := (.inv w84)
private def w86 : CWord := (.mul w85 w9)
private def w87 : CWord := (.mul w83 w86)
private def w88 : CWord := (.comm w15 w10)
private def w89 : CWord := (.mul w14 w88)
private def w90 : CWord := (.sq w57)
private def w91 : CWord := (.mul w26 w90)
private def w92 : CWord := (.mul w91 w70)
private def w93 : CWord := (.comm w82 w90)
private def w94 : CWord := (.comm w82 w26)
private def w95 : CWord := (.comm w94 w90)
private def w96 : CWord := (.comm w82 w91)
private def w97 : CWord := (.comm w96 w70)
private def w98 : CWord := (.comm w82 w70)
private def w99 : CWord := (.mul w98 w94)
private def w100 : CWord := (.comm w82 w92)
private def w101 : CWord := (.comm w100 w15)
private def w102 : CWord := (.comm w15 w90)
private def w103 : CWord := (.comm w15 w26)
private def w104 : CWord := (.comm w103 w90)
private def w105 : CWord := (.comm w15 w91)
private def w106 : CWord := (.comm w105 w70)
private def w107 : CWord := (.comm w15 w70)
private def w108 : CWord := (.mul w107 w103)
private def w109 : CWord := (.comm w83 w92)
private def w110 : CWord := (.comm w109 w86)
private def w111 : CWord := (.mul w99 w108)
private def w112 : CWord := (.comm w86 w92)
private def w113 : CWord := (.comm w87 w92)
private def w114 : CWord := (.comm w113 w89)
private def w115 : CWord := (.comm w89 w92)
private def w116 : CWord := (.mul w19 w46)
private def w117 : CWord := (.mul w11 w25)
private def w118 : CWord := (.mul w117 w27)
private def w119 : CWord := (.mul w118 w30)
private def w120 : CWord := (.mul w116 w119)
private def w121 : CWord := (.mul w11 w42)
private def w122 : CWord := (.mul w121 w45)
private def w123 : CWord := (.mul w122 w48)
private def w124 : CWord := (.mul w123 w53)
private def w125 : CWord := (.mul w90 w70)
private def w126 : CWord := (.comm w9 w125)
private def w127 : CWord := (.comm w126 w17)
private def w128 : CWord := (.mul w126 w127)
private def w129 : CWord := (.comm w17 w90)
private def w130 : CWord := (.comm w17 w70)
private def w131 : CWord := (.comm w129 w70)
private def w132 : CWord := (.comm w19 w125)
private def w133 : CWord := (.comm w132 w46)
private def w134 : CWord := (.comm w46 w90)
private def w135 : CWord := (.comm w46 w70)
private def w136 : CWord := (.comm w134 w70)
private def w137 : CWord := (.comm w116 w125)
private def w138 : CWord := (.comm w137 w119)
private def w139 : CWord := (.mul w130 w135)
private def w140 : CWord := (.comm w119 w125)
private def w141 : CWord := (.comm w120 w125)
private def w142 : CWord := (.comm w141 w124)
private def w143 : CWord := (.comm w124 w125)
private def w144 : CWord := (.comm w1 w0)
private def w145 : CWord := (.comm w144 w2)
private def w146 : CWord := (.sq w145)
private def w147 : CWord := (.comm w3 w2)
private def w148 : CWord := (.sq w147)
private def w149 : CWord := (.mul w146 w148)
private def w150 : CWord := (.comm w1 w54)
private def w151 : CWord := (.comm w150 w1)
private def w152 : CWord := (.sq w151)
private def w153 : CWord := (.mul w149 w152)
private def w154 : CWord := (.comm w144 w1)
private def w155 : CWord := (.comm w154 w2)
private def w156 : CWord := (.mul w153 w155)
private def w157 : CWord := (.comm w151 w1)
private def w158 : CWord := (.mul w156 w157)
private def w159 : CWord := (.comm w154 w1)
private def w160 : CWord := (.mul w158 w159)
private def w161 : CWord := (.comm w144 w0)
private def w162 : CWord := (.comm w161 w1)
private def w163 : CWord := (.comm w148 w146)
private def w164 : CWord := (.sq w146)
private def w165 : CWord := (.sq w148)
private def w166 : CWord := (.mul w164 w165)
private def w167 : CWord := (.comm w163 w148)
private def w168 : CWord := (.comm w152 w149)
private def w169 : CWord := (.sq w152)
private def w170 : CWord := (.mul w166 w169)
private def w171 : CWord := (.comm w168 w152)
private def w172 : CWord := (.comm w155 w153)
private def w173 : CWord := (.sq w155)
private def w174 : CWord := (.mul w170 w173)
private def w175 : CWord := (.comm w172 w155)
private def w176 : CWord := (.comm w157 w156)
private def w177 : CWord := (.sq w157)
private def w178 : CWord := (.mul w174 w177)
private def w179 : CWord := (.comm w176 w157)
private def w180 : CWord := (.comm w159 w158)
private def w181 : CWord := (.sq w159)
private def w182 : CWord := (.mul w178 w181)
private def w183 : CWord := (.comm w180 w159)
private def w184 : CWord := (.comm w162 w160)
private def w185 : CWord := (.sq w162)
private def w186 : CWord := (.mul w182 w185)
private def w187 : CWord := (.comm w184 w162)
private def w188 : CWord := (.comm w146 w2)
private def w189 : CWord := (.comm w188 w148)
private def w190 : CWord := (.comm w149 w2)
private def w191 : CWord := (.comm w190 w152)
private def w192 : CWord := (.comm w148 w2)
private def w193 : CWord := (.mul w188 w192)
private def w194 : CWord := (.comm w153 w2)
private def w195 : CWord := (.comm w194 w155)
private def w196 : CWord := (.comm w152 w2)
private def w197 : CWord := (.mul w193 w196)
private def w198 : CWord := (.comm w156 w2)
private def w199 : CWord := (.comm w198 w157)
private def w200 : CWord := (.comm w155 w2)
private def w201 : CWord := (.mul w197 w200)
private def w202 : CWord := (.comm w158 w2)
private def w203 : CWord := (.comm w202 w159)
private def w204 : CWord := (.comm w157 w2)
private def w205 : CWord := (.mul w201 w204)
private def w206 : CWord := (.comm w160 w2)
private def w207 : CWord := (.comm w206 w162)
private def w208 : CWord := (.comm w159 w2)
private def w209 : CWord := (.mul w205 w208)
private def w210 : CWord := (.mul w1 w31)
private def w211 : CWord := (.comm w146 w31)
private def w212 : CWord := (.comm w146 w1)
private def w213 : CWord := (.comm w212 w31)
private def w214 : CWord := (.comm w146 w210)
private def w215 : CWord := (.comm w214 w148)
private def w216 : CWord := (.comm w148 w31)
private def w217 : CWord := (.comm w148 w1)
private def w218 : CWord := (.comm w217 w31)
private def w219 : CWord := (.comm w149 w210)
private def w220 : CWord := (.comm w219 w152)
private def w221 : CWord := (.mul w212 w217)
private def w222 : CWord := (.comm w152 w31)
private def w223 : CWord := (.comm w152 w1)
private def w224 : CWord := (.comm w223 w31)
private def w225 : CWord := (.comm w153 w210)
private def w226 : CWord := (.comm w225 w155)
private def w227 : CWord := (.mul w221 w223)
private def w228 : CWord := (.comm w155 w31)
private def w229 : CWord := (.comm w155 w1)
private def w230 : CWord := (.comm w229 w31)
private def w231 : CWord := (.comm w156 w210)
private def w232 : CWord := (.comm w231 w157)
private def w233 : CWord := (.mul w227 w229)
private def w234 : CWord := (.comm w157 w31)
private def w235 : CWord := (.comm w157 w1)
private def w236 : CWord := (.comm w235 w31)
private def w237 : CWord := (.comm w158 w210)
private def w238 : CWord := (.comm w237 w159)
private def w239 : CWord := (.mul w233 w235)
private def w240 : CWord := (.comm w159 w31)
private def w241 : CWord := (.comm w159 w1)
private def w242 : CWord := (.comm w241 w31)
private def w243 : CWord := (.comm w160 w210)
private def w244 : CWord := (.comm w243 w162)
private def w245 : CWord := (.mul w239 w241)
private def w246 : CWord := (.comm w162 w31)
private def w247 : CWord := (.comm w162 w1)
private def w248 : CWord := (.comm w247 w31)
private def w249 : CWord := (.sq w154)
private def w250 : CWord := (.mul w0 w75)
private def w251 : CWord := (.comm w249 w75)
private def w252 : CWord := (.comm w249 w0)
private def w253 : CWord := (.comm w252 w75)
private def w254 : CWord := (.comm w249 w250)
private def w255 : CWord := (.comm w254 w159)
private def w256 : CWord := (.comm w159 w75)
private def w257 : CWord := (.comm w159 w0)
private def w258 : CWord := (.comm w257 w75)
private def w259 : CWord := (.mul w84 w152)
private def w260 : CWord := (.mul w259 w249)
private def w261 : CWord := (.mul w260 w157)
private def w262 : CWord := (.comm w2 w84)
private def w263 : CWord := (.comm w262 w152)
private def w264 : CWord := (.comm w2 w152)
private def w265 : CWord := (.mul w264 w262)
private def w266 : CWord := (.comm w2 w259)
private def w267 : CWord := (.comm w266 w249)
private def w268 : CWord := (.comm w2 w249)
private def w269 : CWord := (.mul w268 w265)
private def w270 : CWord := (.comm w2 w260)
private def w271 : CWord := (.comm w270 w157)
private def w272 : CWord := (.comm w2 w157)
private def w273 : CWord := (.mul w272 w269)
private def w274 : CWord := (.comm w2 w261)
private def w275 : CWord := (.comm w274 w162)
private def w276 : CWord := (.comm w2 w162)
private def w277 : CWord := (.mul w276 w273)
private def w278 : CWord := (.sq w150)
private def w279 : CWord := (.sq w278)
private def w280 : CWord := (.mul w279 w152)
private def w281 : CWord := (.comm w150 w54)
private def w282 : CWord := (.sq w281)
private def w283 : CWord := (.mul w280 w282)
private def w284 : CWord := (.comm w281 w1)
private def w285 : CWord := (.comm w54 w279)
private def w286 : CWord := (.comm w285 w152)
private def w287 : CWord := (.comm w54 w152)
private def w288 : CWord := (.mul w287 w285)
private def w289 : CWord := (.comm w54 w280)
private def w290 : CWord := (.comm w289 w282)
private def w291 : CWord := (.comm w54 w282)
private def w292 : CWord := (.mul w291 w288)
private def w293 : CWord := (.comm w54 w283)
private def w294 : CWord := (.comm w293 w284)
private def w295 : CWord := (.comm w54 w284)
private def w296 : CWord := (.mul w295 w292)
private def w297 : CWord := (.mul w15 w86)
private def w298 : CWord := (.mul w9 w89)
private def w299 : CWord := (.mul w17 w46)
private def w300 : CWord := (.mul w25 w27)
private def w301 : CWord := (.mul w27 w30)
private def w302 : CWord := (.mul w25 w301)
private def w303 : CWord := (.mul w11 w302)
private def w304 : CWord := (.mul w46 w303)
private def w305 : CWord := (.mul w42 w45)
private def w306 : CWord := (.mul w45 w48)
private def w307 : CWord := (.mul w42 w306)
private def w308 : CWord := (.mul w48 w53)
private def w309 : CWord := (.mul w17 w304)
private def w310 : CWord := (.mul w45 w308)
private def w311 : CWord := (.mul w42 w310)
private def w312 : CWord := (.mul w11 w311)
private def w313 : CWord := (.mul w27 w312)
private def w314 : CWord := (.mul w85 w298)
private def w315 : CWord := (.mul w15 w314)
private def w316 : CWord := (.mul w29 w313)
private def w317 : CWord := (.mul w27 w316)
private def w318 : CWord := (.mul w25 w317)
private def w319 : CWord := (.mul w11 w318)
private def w320 : CWord := (.mul w46 w319)
private def w321 : CWord := (.mul w17 w320)
private def w322 : CWord := (.mul w9 w321)
private def w323 : CWord := (.mul w88 w322)
private def w324 : CWord := (.sq w55)
private def w325 : CWord := (.comm w55 w54)
private def w326 : CWord := (.sq w325)
private def w327 : CWord := (.mul w59 w326)
private def w328 : CWord := (.mul w58 w327)
private def w329 : CWord := (.mul w324 w328)
private def w330 : CWord := (.mul w14 w323)
private def w331 : CWord := (.mul w9 w330)
private def w332 : CWord := (.mul w85 w331)
private def w333 : CWord := (.mul w15 w332)
private def w334 : CWord := (.mul w84 w329)
private def w335 : CWord := (.mul w53 w334)
private def w336 : CWord := (.mul w62 w61)
private def w337 : CWord := (.comm w61 w54)
private def w338 : CWord := (.mul w66 w337)
private def w339 : CWord := (.mul w337 w74)
private def w340 : CWord := (.mul w66 w339)
private def w341 : CWord := (.mul w68 w340)
private def w342 : CWord := (.mul w61 w341)
private def w343 : CWord := (.mul w62 w342)
private def w344 : CWord := (.mul w71 w78)
private def w345 : CWord := (.mul w48 w335)
private def w346 : CWord := (.mul w45 w345)
private def w347 : CWord := (.mul w42 w346)
private def w348 : CWord := (.mul w11 w347)
private def w349 : CWord := (.mul w27 w348)
private def w350 : CWord := (.mul w29 w349)
private def w351 : CWord := (.mul w27 w350)
private def w352 : CWord := (.mul w25 w351)
private def w353 : CWord := (.mul w11 w352)
private def w354 : CWord := (.mul w46 w353)
private def w355 : CWord := (.mul w17 w354)
private def w356 : CWord := (.mul w9 w355)
private def w357 : CWord := (.mul w88 w356)
private def w358 : CWord := (.mul w14 w357)
private def w359 : CWord := (.mul w9 w358)
private def w360 : CWord := (.mul w85 w359)
private def w361 : CWord := (.mul w15 w360)
private def w362 : CWord := (.mul w73 w344)
private def w363 : CWord := (.mul w337 w362)
private def w364 : CWord := (.mul w66 w363)
private def w365 : CWord := (.mul w68 w364)
private def w366 : CWord := (.mul w61 w365)
private def w367 : CWord := (.mul w62 w366)
private def w368 : CWord := (.mul w64 w367)
private def w369 : CWord := (.mul w326 w368)
private def w370 : CWord := (.mul w94 w108)
private def w371 : CWord := (.mul w103 w139)
private def w372 : CWord := (.mul w59 w369)
private def w373 : CWord := (.mul w58 w372)
private def w374 : CWord := (.mul w324 w373)
private def w375 : CWord := (.mul w84 w374)
private def w376 : CWord := (.mul w53 w375)
private def w377 : CWord := (.mul w48 w376)
private def w378 : CWord := (.mul w45 w377)
private def w379 : CWord := (.mul w42 w378)
private def w380 : CWord := (.mul w11 w379)
private def w381 : CWord := (.mul w27 w380)
private def w382 : CWord := (.mul w29 w381)
private def w383 : CWord := (.mul w27 w382)
private def w384 : CWord := (.mul w25 w383)
private def w385 : CWord := (.mul w11 w384)
private def w386 : CWord := (.mul w46 w385)
private def w387 : CWord := (.mul w17 w386)
private def w388 : CWord := (.mul w9 w387)
private def w389 : CWord := (.mul w88 w388)
private def w390 : CWord := (.mul w14 w389)
private def w391 : CWord := (.mul w9 w390)
private def w392 : CWord := (.mul w85 w391)
private def w393 : CWord := (.mul w15 w392)
private def w394 : CWord := (.mul w107 w371)
private def w395 : CWord := (.mul w94 w394)
private def w396 : CWord := (.mul w98 w395)
private def w397 : CWord := (.mul w78 w396)
private def w398 : CWord := (.mul w165 w169)
private def w399 : CWord := (.mul w169 w173)
private def w400 : CWord := (.mul w165 w399)
private def w401 : CWord := (.mul w173 w177)
private def w402 : CWord := (.mul w169 w401)
private def w403 : CWord := (.mul w165 w402)
private def w404 : CWord := (.mul w177 w181)
private def w405 : CWord := (.mul w173 w404)
private def w406 : CWord := (.mul w169 w405)
private def w407 : CWord := (.mul w165 w406)
private def w408 : CWord := (.mul w181 w185)
private def w409 : CWord := (.mul w192 w196)
private def w410 : CWord := (.mul w196 w200)
private def w411 : CWord := (.mul w192 w410)
private def w412 : CWord := (.mul w200 w204)
private def w413 : CWord := (.mul w196 w412)
private def w414 : CWord := (.mul w192 w413)
private def w415 : CWord := (.mul w204 w208)
private def w416 : CWord := (.comm w162 w2)
private def w417 : CWord := (.mul w200 w415)
private def w418 : CWord := (.mul w196 w417)
private def w419 : CWord := (.mul w192 w418)
private def w420 : CWord := (.mul w208 w416)
private def w421 : CWord := (.mul w177 w408)
private def w422 : CWord := (.mul w173 w421)
private def w423 : CWord := (.mul w169 w422)
private def w424 : CWord := (.mul w165 w423)
private def w425 : CWord := (.mul w204 w420)
private def w426 : CWord := (.mul w200 w425)
private def w427 : CWord := (.mul w196 w426)
private def w428 : CWord := (.mul w192 w427)
private def w429 : CWord := (.mul w188 w428)
private def w430 : CWord := (.mul w185 w429)
private def w431 : CWord := (.mul w217 w223)
private def w432 : CWord := (.mul w223 w229)
private def w433 : CWord := (.mul w217 w432)
private def w434 : CWord := (.mul w229 w235)
private def w435 : CWord := (.mul w223 w434)
private def w436 : CWord := (.mul w217 w435)
private def w437 : CWord := (.mul w235 w241)
private def w438 : CWord := (.mul w229 w437)
private def w439 : CWord := (.mul w223 w438)
private def w440 : CWord := (.mul w217 w439)
private def w441 : CWord := (.mul w241 w247)
private def w442 : CWord := (.mul w181 w430)
private def w443 : CWord := (.mul w177 w442)
private def w444 : CWord := (.mul w173 w443)
private def w445 : CWord := (.mul w169 w444)
private def w446 : CWord := (.mul w165 w445)
private def w447 : CWord := (.mul w235 w441)
private def w448 : CWord := (.mul w229 w447)
private def w449 : CWord := (.mul w223 w448)
private def w450 : CWord := (.mul w217 w449)
private def w451 : CWord := (.mul w212 w450)
private def w452 : CWord := (.mul w416 w451)
private def w453 : CWord := (.mul w208 w452)
private def w454 : CWord := (.mul w204 w453)
private def w455 : CWord := (.mul w200 w454)
private def w456 : CWord := (.mul w196 w455)
private def w457 : CWord := (.mul w192 w456)
private def w458 : CWord := (.mul w188 w457)
private def w459 : CWord := (.mul w185 w458)
private def w460 : CWord := (.mul w181 w459)
private def w461 : CWord := (.mul w177 w460)
private def w462 : CWord := (.mul w173 w461)
private def w463 : CWord := (.mul w169 w462)
private def w464 : CWord := (.mul w165 w463)
private def w465 : CWord := (.mul w252 w257)
private def w466 : CWord := (.mul w247 w465)
private def w467 : CWord := (.mul w241 w466)
private def w468 : CWord := (.mul w235 w467)
private def w469 : CWord := (.mul w229 w468)
private def w470 : CWord := (.mul w223 w469)
private def w471 : CWord := (.mul w217 w470)
private def w472 : CWord := (.mul w212 w471)
private def w473 : CWord := (.mul w416 w472)
private def w474 : CWord := (.mul w208 w473)
private def w475 : CWord := (.mul w204 w474)
private def w476 : CWord := (.mul w200 w475)
private def w477 : CWord := (.mul w196 w476)
private def w478 : CWord := (.mul w192 w477)
private def w479 : CWord := (.mul w188 w478)
private def w480 : CWord := (.mul w185 w479)
private def w481 : CWord := (.mul w181 w480)
private def w482 : CWord := (.mul w177 w481)
private def w483 : CWord := (.mul w173 w482)
private def w484 : CWord := (.mul w169 w483)
private def w485 : CWord := (.mul w165 w484)
private def w486 : CWord := (.mul w257 w277)
private def w487 : CWord := (.mul w252 w486)
private def w488 : CWord := (.mul w247 w487)
private def w489 : CWord := (.mul w241 w488)
private def w490 : CWord := (.mul w235 w489)
private def w491 : CWord := (.mul w229 w490)
private def w492 : CWord := (.mul w223 w491)
private def w493 : CWord := (.mul w217 w492)
private def w494 : CWord := (.mul w212 w493)
private def w495 : CWord := (.mul w416 w494)
private def w496 : CWord := (.mul w208 w495)
private def w497 : CWord := (.mul w204 w496)
private def w498 : CWord := (.mul w200 w497)
private def w499 : CWord := (.mul w196 w498)
private def w500 : CWord := (.mul w192 w499)
private def w501 : CWord := (.mul w188 w500)
private def w502 : CWord := (.mul w185 w501)
private def w503 : CWord := (.mul w181 w502)
private def w504 : CWord := (.mul w177 w503)
private def w505 : CWord := (.mul w173 w504)
private def w506 : CWord := (.mul w169 w505)
private def w507 : CWord := (.mul w165 w506)
private def w508 : CWord := (.mul w262 w296)
private def w509 : CWord := (.mul w71 w397)
private def w510 : CWord := (.mul w73 w509)
private def w511 : CWord := (.mul w337 w510)
private def w512 : CWord := (.mul w66 w511)
private def w513 : CWord := (.mul w68 w512)
private def w514 : CWord := (.mul w61 w513)
private def w515 : CWord := (.mul w62 w514)
private def w516 : CWord := (.mul w64 w515)
private def w517 : CWord := (.mul w326 w516)
private def w518 : CWord := (.mul w59 w517)
private def w519 : CWord := (.mul w58 w518)
private def w520 : CWord := (.mul w324 w519)
private def w521 : CWord := (.mul w84 w520)
private def w522 : CWord := (.mul w53 w521)
private def w523 : CWord := (.mul w48 w522)
private def w524 : CWord := (.mul w45 w523)
private def w525 : CWord := (.mul w42 w524)
private def w526 : CWord := (.mul w11 w525)
private def w527 : CWord := (.mul w27 w526)
private def w528 : CWord := (.mul w29 w527)
private def w529 : CWord := (.mul w27 w528)
private def w530 : CWord := (.mul w25 w529)
private def w531 : CWord := (.mul w11 w530)
private def w532 : CWord := (.mul w46 w531)
private def w533 : CWord := (.mul w17 w532)
private def w534 : CWord := (.mul w9 w533)
private def w535 : CWord := (.mul w88 w534)
private def w536 : CWord := (.mul w14 w535)
private def w537 : CWord := (.mul w9 w536)
private def w538 : CWord := (.mul w85 w537)
private def w539 : CWord := (.mul w15 w538)
private def w540 : CWord := (.mul w264 w508)
private def w541 : CWord := (.mul w268 w540)
private def w542 : CWord := (.mul w272 w541)
private def w543 : CWord := (.mul w276 w542)
private def w544 : CWord := (.mul w257 w543)
private def w545 : CWord := (.mul w252 w544)
private def w546 : CWord := (.mul w247 w545)
private def w547 : CWord := (.mul w241 w546)
private def w548 : CWord := (.mul w235 w547)
private def w549 : CWord := (.mul w229 w548)
private def w550 : CWord := (.mul w223 w549)
private def w551 : CWord := (.mul w217 w550)
private def w552 : CWord := (.mul w212 w551)
private def w553 : CWord := (.mul w416 w552)
private def w554 : CWord := (.mul w208 w553)
private def w555 : CWord := (.mul w204 w554)
private def w556 : CWord := (.mul w200 w555)
private def w557 : CWord := (.mul w196 w556)
private def w558 : CWord := (.mul w192 w557)
private def w559 : CWord := (.mul w188 w558)
private def w560 : CWord := (.mul w185 w559)
private def w561 : CWord := (.mul w181 w560)
private def w562 : CWord := (.mul w177 w561)
private def w563 : CWord := (.mul w173 w562)
private def w564 : CWord := (.mul w169 w563)
private def w565 : CWord := (.mul w165 w564)
private def w566 : CWord := (.mul w164 w565)
private def w567 : CWord := (.mul w135 w566)
private def w568 : CWord := (.mul w130 w567)
private def w569 : CWord := (.mul w103 w568)
private def w570 : CWord := (.mul w107 w569)
private def w571 : CWord := (.mul w94 w570)
private def w572 : CWord := (.mul w98 w571)
private def w573 : CWord := (.mul w78 w572)
private def w574 : CWord := (.mul w71 w573)
private def w575 : CWord := (.mul w73 w574)
private def w576 : CWord := (.mul w337 w575)
private def w577 : CWord := (.mul w66 w576)
private def w578 : CWord := (.mul w68 w577)
private def w579 : CWord := (.mul w61 w578)
private def w580 : CWord := (.mul w62 w579)
private def w581 : CWord := (.mul w64 w580)
private def w582 : CWord := (.mul w326 w581)
private def w583 : CWord := (.mul w59 w582)
private def w584 : CWord := (.mul w58 w583)
private def w585 : CWord := (.mul w324 w584)
private def w586 : CWord := (.comm w53 w84)
private def w587 : CWord := (.mul w84 w53)
private def w588 : CWord := (.mul w53 w585)
private def w589 : CWord := (.comm w48 w84)
private def w590 : CWord := (.mul w84 w48)
private def w591 : CWord := (.mul w48 w588)
private def w592 : CWord := (.comm w45 w84)
private def w593 : CWord := (.mul w84 w45)
private def w594 : CWord := (.mul w45 w591)
private def w595 : CWord := (.comm w42 w84)
private def w596 : CWord := (.mul w84 w42)
private def w597 : CWord := (.mul w42 w594)
private def w598 : CWord := (.comm w11 w84)
private def w599 : CWord := (.mul w84 w11)
private def w600 : CWord := (.mul w11 w597)
private def w601 : CWord := (.comm w27 w84)
private def w602 : CWord := (.mul w84 w27)
private def w603 : CWord := (.mul w27 w600)
private def w604 : CWord := (.comm w29 w84)
private def w605 : CWord := (.mul w84 w29)
private def w606 : CWord := (.mul w29 w603)
private def w607 : CWord := (.mul w27 w606)
private def w608 : CWord := (.comm w25 w84)
private def w609 : CWord := (.mul w84 w25)
private def w610 : CWord := (.mul w25 w607)
private def w611 : CWord := (.mul w11 w610)
private def w612 : CWord := (.comm w46 w84)
private def w613 : CWord := (.mul w84 w46)
private def w614 : CWord := (.mul w46 w611)
private def w615 : CWord := (.comm w17 w84)
private def w616 : CWord := (.mul w84 w17)
private def w617 : CWord := (.mul w17 w614)
private def w618 : CWord := (.comm w9 w84)
private def w619 : CWord := (.mul w84 w9)
private def w620 : CWord := (.mul w9 w617)
private def w621 : CWord := (.comm w88 w84)
private def w622 : CWord := (.mul w84 w88)
private def w623 : CWord := (.mul w88 w620)
private def w624 : CWord := (.comm w14 w84)
private def w625 : CWord := (.mul w84 w14)
private def w626 : CWord := (.mul w14 w623)
private def w627 : CWord := (.mul w9 w626)
private def w628 : CWord := (.inv w15)
private def w629 : CWord := (.comm w9 w628)
private def w630 : CWord := (.mul w628 w9)
private def w631 : CWord := (.mul w9 w614)
private def w632 : CWord := (.comm w88 w628)
private def w633 : CWord := (.mul w628 w88)
private def w634 : CWord := (.mul w88 w631)
private def w635 : CWord := (.comm w14 w628)
private def w636 : CWord := (.mul w628 w14)
private def w637 : CWord := (.mul w14 w634)
private def w638 : CWord := (.mul w9 w637)
private def w639 : CWord := (.comm w46 w35)
private def w640 : CWord := (.mul w35 w46)
private def w641 : CWord := (.mul w46 w610)
private def w642 : CWord := (.comm w9 w35)
private def w643 : CWord := (.mul w35 w9)
private def w644 : CWord := (.mul w9 w641)
private def w645 : CWord := (.comm w88 w35)
private def w646 : CWord := (.mul w35 w88)
private def w647 : CWord := (.mul w88 w644)
private def w648 : CWord := (.comm w42 w43)
private def w649 : CWord := (.mul w43 w42)
private def w650 : CWord := (.mul w42 w591)
private def w651 : CWord := (.comm w11 w43)
private def w652 : CWord := (.mul w43 w11)
private def w653 : CWord := (.mul w11 w650)
private def w654 : CWord := (.comm w27 w43)
private def w655 : CWord := (.mul w43 w27)
private def w656 : CWord := (.mul w27 w653)
private def w657 : CWord := (.inv w64)
private def w658 : CWord := (.comm w66 w657)
private def w659 : CWord := (.mul w657 w66)
private def w660 : CWord := (.mul w66 w575)
private def w661 : CWord := (.comm w68 w657)
private def w662 : CWord := (.mul w657 w68)
private def w663 : CWord := (.mul w68 w660)
private def w664 : CWord := (.comm w61 w657)
private def w665 : CWord := (.mul w657 w61)
private def w666 : CWord := (.mul w61 w663)
private def w667 : CWord := (.comm w62 w657)
private def w668 : CWord := (.mul w657 w62)
private def w669 : CWord := (.mul w62 w666)
private def w670 : CWord := (.inv w73)
private def w671 : CWord := (.comm w71 w670)
private def w672 : CWord := (.mul w670 w71)
private def w673 : CWord := (.mul w71 w572)
private def w674 : CWord := (.inv w196)
private def w675 : CWord := (.comm w268 w674)
private def w676 : CWord := (.mul w674 w268)
private def w677 : CWord := (.mul w268 w508)
private def w678 : CWord := (.comm w272 w674)
private def w679 : CWord := (.mul w674 w272)
private def w680 : CWord := (.mul w272 w677)
private def w681 : CWord := (.comm w276 w674)
private def w682 : CWord := (.mul w674 w276)
private def w683 : CWord := (.mul w276 w680)
private def w684 : CWord := (.comm w257 w674)
private def w685 : CWord := (.mul w674 w257)
private def w686 : CWord := (.mul w257 w683)
private def w687 : CWord := (.comm w252 w674)
private def w688 : CWord := (.mul w674 w252)
private def w689 : CWord := (.mul w252 w686)
private def w690 : CWord := (.comm w247 w674)
private def w691 : CWord := (.mul w674 w247)
private def w692 : CWord := (.mul w247 w689)
private def w693 : CWord := (.comm w241 w674)
private def w694 : CWord := (.mul w674 w241)
private def w695 : CWord := (.mul w241 w692)
private def w696 : CWord := (.comm w235 w674)
private def w697 : CWord := (.mul w674 w235)
private def w698 : CWord := (.mul w235 w695)
private def w699 : CWord := (.comm w229 w674)
private def w700 : CWord := (.mul w674 w229)
private def w701 : CWord := (.mul w229 w698)
private def w702 : CWord := (.comm w223 w674)
private def w703 : CWord := (.mul w674 w223)
private def w704 : CWord := (.mul w223 w701)
private def w705 : CWord := (.comm w217 w674)
private def w706 : CWord := (.mul w674 w217)
private def w707 : CWord := (.mul w217 w704)
private def w708 : CWord := (.comm w212 w674)
private def w709 : CWord := (.mul w674 w212)
private def w710 : CWord := (.mul w212 w707)
private def w711 : CWord := (.comm w416 w674)
private def w712 : CWord := (.mul w674 w416)
private def w713 : CWord := (.mul w416 w710)
private def w714 : CWord := (.comm w208 w674)
private def w715 : CWord := (.mul w674 w208)
private def w716 : CWord := (.mul w208 w713)
private def w717 : CWord := (.comm w204 w674)
private def w718 : CWord := (.mul w674 w204)
private def w719 : CWord := (.mul w204 w716)
private def w720 : CWord := (.comm w200 w674)
private def w721 : CWord := (.mul w674 w200)
private def w722 : CWord := (.mul w200 w719)
private def w723 : CWord := (.inv w204)
private def w724 : CWord := (.comm w276 w723)
private def w725 : CWord := (.mul w723 w276)
private def w726 : CWord := (.mul w276 w677)
private def w727 : CWord := (.comm w257 w723)
private def w728 : CWord := (.mul w723 w257)
private def w729 : CWord := (.mul w257 w726)
private def w730 : CWord := (.comm w252 w723)
private def w731 : CWord := (.mul w723 w252)
private def w732 : CWord := (.mul w252 w729)
private def w733 : CWord := (.comm w247 w723)
private def w734 : CWord := (.mul w723 w247)
private def w735 : CWord := (.mul w247 w732)
private def w736 : CWord := (.comm w241 w723)
private def w737 : CWord := (.mul w723 w241)
private def w738 : CWord := (.mul w241 w735)
private def w739 : CWord := (.comm w235 w723)
private def w740 : CWord := (.mul w723 w235)
private def w741 : CWord := (.mul w235 w738)
private def w742 : CWord := (.comm w229 w723)
private def w743 : CWord := (.mul w723 w229)
private def w744 : CWord := (.mul w229 w741)
private def w745 : CWord := (.comm w223 w723)
private def w746 : CWord := (.mul w723 w223)
private def w747 : CWord := (.mul w223 w744)
private def w748 : CWord := (.comm w217 w723)
private def w749 : CWord := (.mul w723 w217)
private def w750 : CWord := (.mul w217 w747)
private def w751 : CWord := (.comm w212 w723)
private def w752 : CWord := (.mul w723 w212)
private def w753 : CWord := (.mul w212 w750)
private def w754 : CWord := (.comm w416 w723)
private def w755 : CWord := (.mul w723 w416)
private def w756 : CWord := (.mul w416 w753)
private def w757 : CWord := (.comm w208 w723)
private def w758 : CWord := (.mul w723 w208)
private def w759 : CWord := (.mul w208 w756)
private def w760 : CWord := (.inv w416)
private def w761 : CWord := (.comm w257 w760)
private def w762 : CWord := (.mul w760 w257)
private def w763 : CWord := (.mul w257 w677)
private def w764 : CWord := (.comm w252 w760)
private def w765 : CWord := (.mul w760 w252)
private def w766 : CWord := (.mul w252 w763)
private def w767 : CWord := (.comm w247 w760)
private def w768 : CWord := (.mul w760 w247)
private def w769 : CWord := (.mul w247 w766)
private def w770 : CWord := (.comm w241 w760)
private def w771 : CWord := (.mul w760 w241)
private def w772 : CWord := (.mul w241 w769)
private def w773 : CWord := (.comm w235 w760)
private def w774 : CWord := (.mul w760 w235)
private def w775 : CWord := (.mul w235 w772)
private def w776 : CWord := (.comm w229 w760)
private def w777 : CWord := (.mul w760 w229)
private def w778 : CWord := (.mul w229 w775)
private def w779 : CWord := (.comm w223 w760)
private def w780 : CWord := (.mul w760 w223)
private def w781 : CWord := (.mul w223 w778)
private def w782 : CWord := (.comm w217 w760)
private def w783 : CWord := (.mul w760 w217)
private def w784 : CWord := (.mul w217 w781)
private def w785 : CWord := (.comm w212 w760)
private def w786 : CWord := (.mul w760 w212)
private def w787 : CWord := (.mul w212 w784)
private def w788 : CWord := (.mul w208 w787)
private def w789 : CWord := (.mul w200 w788)
private def w790 : CWord := (.mul w192 w789)
private def w791 : CWord := (.mul w188 w790)
private def w792 : CWord := (.mul w185 w791)
private def w793 : CWord := (.mul w181 w792)
private def w794 : CWord := (.mul w177 w793)
private def w795 : CWord := (.mul w173 w794)
private def w796 : CWord := (.mul w169 w795)
private def w797 : CWord := (.mul w165 w796)
private def w798 : CWord := (.mul w164 w797)
private def w799 : CWord := (.mul w135 w798)
private def w800 : CWord := (.mul w130 w799)
private def w801 : CWord := (.mul w103 w800)
private def w802 : CWord := (.mul w107 w801)
private def w803 : CWord := (.mul w94 w802)
private def w804 : CWord := (.mul w98 w803)
private def w805 : CWord := (.mul w71 w804)
private def w806 : CWord := (.mul w66 w805)
private def w807 : CWord := (.mul w68 w806)
private def w808 : CWord := (.mul w61 w807)
private def w809 : CWord := (.mul w62 w808)
private def w810 : CWord := (.mul w326 w809)
private def w811 : CWord := (.mul w59 w810)
private def w812 : CWord := (.mul w58 w811)
private def w813 : CWord := (.mul w324 w812)
private def w814 : CWord := (.mul w53 w813)
private def w815 : CWord := (.mul w48 w814)
private def w816 : CWord := (.mul w42 w815)
private def w817 : CWord := (.mul w11 w816)
private def w818 : CWord := (.mul w27 w817)
private def w819 : CWord := (.mul w27 w818)
private def w820 : CWord := (.mul w25 w819)
private def w821 : CWord := (.mul w46 w820)
private def w822 : CWord := (.comm w88 w9)
private def w823 : CWord := (.mul w9 w88)
private def w824 : CWord := (.mul w88 w821)
private def w825 : CWord := (.sq w9)
private def w826 : CWord := (.sq w27)

private def trace0 : Deriv :=
  (.mul
  (.mul
    (.mul
      (.mul
        (.mul
          (.mul
            (.mul
              (.mul
                (.sq
                  (.comm
                    (.refl w0)
                    (.refl w1)
                  )
                )
                (.comm
                  (.comm
                    (.refl w0)
                    (.refl w1)
                  )
                  (.refl w2)
                )
              )
              (.mul
                (.symm
                  (.inv_sq w4)
                )
                (.trans
                  (.comm_inv_left w4 w2)
                  (.trans
                    (.mul
                      (.inv_comm w4 w2)
                      (.deep w8)
                    )
                    (.mul_one w9)
                  )
                )
              )
            )
            (.mul
              (.trans
                (.mul
                  (.trans
                    (.comm_inv_right w10 w4)
                    (.trans
                      (.mul
                        (.inv_comm w10 w4)
                        (.deep w13)
                      )
                      (.mul_one w14)
                    )
                  )
                  (.deep w16)
                )
                (.mul_one w14)
              )
              (.comm
                (.comm
                  (.comm
                    (.refl w0)
                    (.refl w1)
                  )
                  (.refl w2)
                )
                (.comm
                  (.refl w0)
                  (.refl w1)
                )
              )
            )
          )
          (.mul
            (.mul
              (.mul
                (.trans
                  (.comm_mul_right w2 w10 w4)
                  (.trans
                    (.mul
                      (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                      )
                      (.deep w18)
                    )
                    (.mul_one w19)
                  )
                )
                (.comm
                  (.comm
                    (.refl w0)
                    (.refl w1)
                  )
                  (.refl w1)
                )
              )
              (.mul
                (.mul
                  (.mul
                    (.trans
                      (.comm_mul_right w10 w10 w4)
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm_self w10)
                        )
                        (.mul_one w11)
                        )
                        (.deep w21)
                        )
                        (.mul_one w11)
                      )
                    )
                    (.trans
                      (.comm_inv_left w4 w1)
                      (.trans
                        (.mul
                        (.inv_comm w4 w1)
                        (.deep w24)
                        )
                        (.mul_one w25)
                      )
                    )
                  )
                  (.comm
                    (.comm
                      (.refl w2)
                      (.refl w1)
                    )
                    (.comm
                      (.refl w0)
                      (.refl w1)
                    )
                  )
                )
                (.trans
                  (.comm_mul_right w26 w10 w4)
                  (.trans
                    (.mul
                      (.mul
                        (.comm
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                      )
                      (.deep w28)
                    )
                    (.mul_one w30)
                  )
                )
              )
            )
            (.mul
              (.mul
                (.mul
                  (.mul
                    (.trans
                      (.mul
                        (.deep w33)
                        (.trans
                        (.comm_mul_right w7 w10 w4)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w34)
                        (.trans
                        (.comm_inv_left w4 w10)
                        (.trans
                        (.mul
                        (.inv_comm w4 w10)
                        (.deep w36)
                        )
                        (.mul_one w11)
                        )
                        )
                        )
                        (.one_mul w11)
                        )
                        (.deep w38)
                        )
                        (.mul_one w11)
                        )
                        )
                      )
                      (.one_mul w11)
                    )
                    (.trans
                      (.trans
                        (.comm
                        (.trans
                        (.comm_mul_right w2 w10 w4)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w18)
                        )
                        (.mul_one w19)
                        )
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm_mul_left w9 w17 w10)
                      )
                      (.trans
                        (.mul
                        (.deep w41)
                        (.comm
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.one_mul w42)
                      )
                    )
                  )
                  (.trans
                    (.comm_inv_right w26 w4)
                    (.trans
                      (.mul
                        (.inv_comm w26 w4)
                        (.deep w44)
                      )
                      (.mul_one w45)
                    )
                  )
                )
                (.trans
                  (.comm_mul_right w46 w10 w4)
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.deep w47)
                        (.comm
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.one_mul w48)
                      )
                      (.deep w49)
                    )
                    (.mul_one w48)
                  )
                )
              )
              (.trans
                (.trans
                  (.comm
                    (.trans
                      (.comm_mul_right w2 w10 w4)
                      (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w18)
                        )
                        (.mul_one w19)
                      )
                    )
                    (.comm
                      (.refl w2)
                      (.refl w1)
                    )
                  )
                  (.comm_mul_left w9 w17 w26)
                )
                (.trans
                  (.mul
                    (.deep w52)
                    (.comm
                      (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                      )
                      (.comm
                        (.refl w2)
                        (.refl w1)
                      )
                    )
                  )
                  (.one_mul w53)
                )
              )
            )
          )
        )
        (.mul
          (.mul
            (.sq
              (.sq
                (.sq
                  (.refl w1)
                )
              )
            )
            (.sq
              (.comm
                (.refl w54)
                (.sq
                  (.refl w1)
                )
              )
            )
          )
          (.mul
            (.trans
              (.mul
                (.mul
                  (.comm
                    (.sq
                      (.refl w54)
                    )
                    (.sq
                      (.sq
                        (.refl w1)
                      )
                    )
                  )
                  (.comm
                    (.comm
                      (.refl w54)
                      (.sq
                        (.refl w1)
                      )
                    )
                    (.sq
                      (.refl w54)
                    )
                  )
                )
                (.deep w56)
              )
              (.mul_one w60)
            )
            (.sq
              (.comm
                (.comm
                  (.refl w54)
                  (.sq
                    (.refl w1)
                  )
                )
                (.refl w54)
              )
            )
          )
        )
      )
      (.mul
        (.mul
          (.mul
            (.trans
              (.comm_mul_right w54 w4 w61)
              (.trans
                (.mul
                  (.mul
                    (.comm
                      (.refl w54)
                      (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w0)
                      )
                    )
                    (.comm
                      (.refl w54)
                      (.sq
                        (.sq
                        (.refl w1)
                        )
                      )
                    )
                  )
                  (.deep w63)
                )
                (.mul_one w65)
              )
            )
            (.comm
              (.sq
                (.refl w1)
              )
              (.refl w0)
            )
          )
          (.mul
            (.mul
              (.trans
                (.comm_mul_right w3 w4 w61)
                (.trans
                  (.mul
                    (.mul
                      (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w0)
                        )
                      )
                      (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                      )
                    )
                    (.deep w67)
                  )
                  (.mul_one w69)
                )
              )
              (.comm
                (.comm
                  (.sq
                    (.refl w1)
                  )
                  (.refl w0)
                )
                (.refl w54)
              )
            )
            (.trans
              (.comm_mul_right w70 w4 w61)
              (.trans
                (.mul
                  (.mul
                    (.comm
                      (.comm
                        (.refl w54)
                        (.refl w0)
                      )
                      (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w0)
                      )
                    )
                    (.comm
                      (.comm
                        (.refl w54)
                        (.refl w0)
                      )
                      (.sq
                        (.sq
                        (.refl w1)
                        )
                      )
                    )
                  )
                  (.deep w72)
                )
                (.mul_one w74)
              )
            )
          )
        )
        (.trans
          (.mul
            (.trans
              (.mul
                (.trans
                  (.mul
                    (.deep w77)
                    (.comm
                      (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w0)
                      )
                      (.comm
                        (.refl w54)
                        (.refl w0)
                      )
                    )
                  )
                  (.one_mul w78)
                )
                (.deep w80)
              )
              (.mul_one w78)
            )
            (.deep w81)
          )
          (.mul_one w78)
        )
      )
    )
    (.mul
      (.trans
        (.trans
          (.comm
            (.mul
              (.mul
                (.mul
                  (.sq
                    (.comm
                      (.refl w0)
                      (.refl w1)
                    )
                  )
                  (.comm
                    (.comm
                      (.refl w0)
                      (.refl w1)
                    )
                    (.refl w2)
                  )
                )
                (.mul
                  (.symm
                    (.inv_sq w4)
                  )
                  (.trans
                    (.comm_inv_left w4 w2)
                    (.trans
                      (.mul
                        (.inv_comm w4 w2)
                        (.deep w8)
                      )
                      (.mul_one w9)
                    )
                  )
                )
              )
              (.mul
                (.trans
                  (.mul
                    (.trans
                      (.comm_inv_right w10 w4)
                      (.trans
                        (.mul
                        (.inv_comm w10 w4)
                        (.deep w13)
                        )
                        (.mul_one w14)
                      )
                    )
                    (.deep w16)
                  )
                  (.mul_one w14)
                )
                (.comm
                  (.comm
                    (.comm
                      (.refl w0)
                      (.refl w1)
                    )
                    (.refl w2)
                  )
                  (.comm
                    (.refl w0)
                    (.refl w1)
                  )
                )
              )
            )
            (.mul
              (.mul
                (.comm
                  (.refl w2)
                  (.refl w1)
                )
                (.sq
                  (.sq
                    (.refl w54)
                  )
                )
              )
              (.comm
                (.refl w54)
                (.refl w0)
              )
            )
          )
          (.comm_mul_left w87 w89 w92)
        )
        (.trans
          (.mul
            (.trans
              (.mul
                (.trans
                  (.comm_mul_left w83 w86 w92)
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w82 w15 w92)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_right w82 w91 w70)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.sq
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm
                        (.refl w54)
                        (.refl w0)
                        )
                        )
                        (.trans
                        (.comm_mul_right w82 w26 w90)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w93)
                        (.comm
                        (.sq
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                        )
                        )
                        (.one_mul w94)
                        )
                        (.deep w95)
                        )
                        (.mul_one w94)
                        )
                        )
                        )
                        (.deep w97)
                        )
                        (.mul_one w99)
                        )
                        )
                        (.deep w101)
                        )
                        (.mul_one w99)
                        )
                        (.trans
                        (.comm_mul_right w15 w91 w70)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        (.comm
                        (.refl w54)
                        (.refl w0)
                        )
                        )
                        (.trans
                        (.comm_mul_right w15 w26 w90)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w102)
                        (.comm
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                        )
                        )
                        (.one_mul w103)
                        )
                        (.deep w104)
                        )
                        (.mul_one w103)
                        )
                        )
                        )
                        (.deep w106)
                        )
                        (.mul_one w108)
                        )
                        )
                        )
                        )
                        (.deep w110)
                        )
                        (.mul_one w111)
                      )
                      (.deep w112)
                    )
                    (.mul_one w111)
                  )
                )
                (.deep w114)
              )
              (.mul_one w111)
            )
            (.deep w115)
          )
          (.mul_one w111)
        )
      )
      (.trans
        (.trans
          (.comm
            (.mul
              (.mul
                (.mul
                  (.trans
                    (.comm_mul_right w2 w10 w4)
                    (.trans
                      (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w18)
                      )
                      (.mul_one w19)
                    )
                  )
                  (.comm
                    (.comm
                      (.refl w0)
                      (.refl w1)
                    )
                    (.refl w1)
                  )
                )
                (.mul
                  (.mul
                    (.mul
                      (.trans
                        (.comm_mul_right w10 w10 w4)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm_self w10)
                        )
                        (.mul_one w11)
                        )
                        (.deep w21)
                        )
                        (.mul_one w11)
                        )
                      )
                      (.trans
                        (.comm_inv_left w4 w1)
                        (.trans
                        (.mul
                        (.inv_comm w4 w1)
                        (.deep w24)
                        )
                        (.mul_one w25)
                        )
                      )
                    )
                    (.comm
                      (.comm
                        (.refl w2)
                        (.refl w1)
                      )
                      (.comm
                        (.refl w0)
                        (.refl w1)
                      )
                    )
                  )
                  (.trans
                    (.comm_mul_right w26 w10 w4)
                    (.trans
                      (.mul
                        (.mul
                        (.comm
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w28)
                      )
                      (.mul_one w30)
                    )
                  )
                )
              )
              (.mul
                (.mul
                  (.mul
                    (.mul
                      (.trans
                        (.mul
                        (.deep w33)
                        (.trans
                        (.comm_mul_right w7 w10 w4)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w34)
                        (.trans
                        (.comm_inv_left w4 w10)
                        (.trans
                        (.mul
                        (.inv_comm w4 w10)
                        (.deep w36)
                        )
                        (.mul_one w11)
                        )
                        )
                        )
                        (.one_mul w11)
                        )
                        (.deep w38)
                        )
                        (.mul_one w11)
                        )
                        )
                        )
                        (.one_mul w11)
                      )
                      (.trans
                        (.trans
                        (.comm
                        (.trans
                        (.comm_mul_right w2 w10 w4)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w18)
                        )
                        (.mul_one w19)
                        )
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm_mul_left w9 w17 w10)
                        )
                        (.trans
                        (.mul
                        (.deep w41)
                        (.comm
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.one_mul w42)
                        )
                      )
                    )
                    (.trans
                      (.comm_inv_right w26 w4)
                      (.trans
                        (.mul
                        (.inv_comm w26 w4)
                        (.deep w44)
                        )
                        (.mul_one w45)
                      )
                    )
                  )
                  (.trans
                    (.comm_mul_right w46 w10 w4)
                    (.trans
                      (.mul
                        (.trans
                        (.mul
                        (.deep w47)
                        (.comm
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.one_mul w48)
                        )
                        (.deep w49)
                      )
                      (.mul_one w48)
                    )
                  )
                )
                (.trans
                  (.trans
                    (.comm
                      (.trans
                        (.comm_mul_right w2 w10 w4)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w18)
                        )
                        (.mul_one w19)
                        )
                      )
                      (.comm
                        (.refl w2)
                        (.refl w1)
                      )
                    )
                    (.comm_mul_left w9 w17 w26)
                  )
                  (.trans
                    (.mul
                      (.deep w52)
                      (.comm
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.refl w1)
                        )
                      )
                    )
                    (.one_mul w53)
                  )
                )
              )
            )
            (.mul
              (.sq
                (.sq
                  (.refl w54)
                )
              )
              (.comm
                (.refl w54)
                (.refl w0)
              )
            )
          )
          (.comm_mul_left w120 w124 w125)
        )
        (.trans
          (.mul
            (.trans
              (.mul
                (.trans
                  (.comm_mul_left w116 w119 w125)
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w19 w46 w125)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w9 w17 w125)
                        (.trans
                        (.mul
                        (.deep w128)
                        (.trans
                        (.comm_mul_right w17 w90 w70)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.refl w2)
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        )
                        (.comm
                        (.refl w54)
                        (.refl w0)
                        )
                        )
                        (.deep w129)
                        )
                        (.mul_one w130)
                        )
                        (.deep w131)
                        )
                        (.mul_one w130)
                        )
                        )
                        )
                        (.one_mul w130)
                        )
                        )
                        (.deep w133)
                        )
                        (.mul_one w130)
                        )
                        (.trans
                        (.comm_mul_right w46 w90 w70)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.comm
                        (.comm
                        (.refl w0)
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.comm
                        (.refl w54)
                        (.refl w0)
                        )
                        )
                        (.deep w134)
                        )
                        (.mul_one w135)
                        )
                        (.deep w136)
                        )
                        (.mul_one w135)
                        )
                        )
                        )
                        )
                        (.deep w138)
                        )
                        (.mul_one w139)
                      )
                      (.deep w140)
                    )
                    (.mul_one w139)
                  )
                )
                (.deep w142)
              )
              (.mul_one w139)
            )
            (.deep w143)
          )
          (.mul_one w139)
        )
      )
    )
  )
  (.mul
    (.mul
      (.mul
        (.mul
          (.mul
            (.trans
              (.sq_mul w160 w162)
              (.trans
                (.mul
                  (.trans
                    (.mul
                      (.mul
                        (.trans
                        (.sq_mul w158 w159)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.trans
                        (.sq_mul w156 w157)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.trans
                        (.sq_mul w153 w155)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.trans
                        (.sq_mul w149 w152)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.trans
                        (.sq_mul w146 w148)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.sq
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w2)
                        )
                        )
                        )
                        (.sq
                        (.sq
                        (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        )
                        )
                        )
                        (.deep w163)
                        )
                        (.mul_one w166)
                        )
                        (.deep w167)
                        )
                        (.mul_one w166)
                        )
                        )
                        (.sq
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        )
                        )
                        )
                        (.deep w168)
                        )
                        (.mul_one w170)
                        )
                        (.deep w171)
                        )
                        (.mul_one w170)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        )
                        )
                        (.deep w172)
                        )
                        (.mul_one w174)
                        )
                        (.deep w175)
                        )
                        (.mul_one w174)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w176)
                        )
                        (.mul_one w178)
                        )
                        (.deep w179)
                        )
                        (.mul_one w178)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        )
                        )
                        (.deep w180)
                        )
                        (.mul_one w182)
                        )
                        (.deep w183)
                        )
                        (.mul_one w182)
                        )
                        )
                        (.sq
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        )
                      )
                      (.deep w184)
                    )
                    (.mul_one w186)
                  )
                  (.deep w187)
                )
                (.mul_one w186)
              )
            )
            (.trans
              (.comm_mul_left w160 w162 w2)
              (.mul
                (.trans
                  (.mul
                    (.trans
                      (.comm_mul_left w158 w159 w2)
                      (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w156 w157 w2)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w153 w155 w2)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w149 w152 w2)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w146 w148 w2)
                        (.mul
                        (.trans
                        (.mul
                        (.comm
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w2)
                        )
                        )
                        (.refl w2)
                        )
                        (.deep w189)
                        )
                        (.mul_one w188)
                        )
                        (.comm
                        (.sq
                        (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        )
                        (.refl w2)
                        )
                        )
                        )
                        (.deep w191)
                        )
                        (.mul_one w193)
                        )
                        (.comm
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        )
                        (.refl w2)
                        )
                        )
                        )
                        (.deep w195)
                        )
                        (.mul_one w197)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        (.refl w2)
                        )
                        )
                        )
                        (.deep w199)
                        )
                        (.mul_one w201)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        )
                        )
                        (.deep w203)
                        )
                        (.mul_one w205)
                        )
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                      )
                    )
                    (.deep w207)
                  )
                  (.mul_one w209)
                )
                (.comm
                  (.comm
                    (.comm
                      (.comm
                        (.refl w1)
                        (.refl w0)
                      )
                      (.refl w0)
                    )
                    (.refl w1)
                  )
                  (.refl w2)
                )
              )
            )
          )
          (.trans
            (.comm_mul_left w160 w162 w210)
            (.mul
              (.trans
                (.mul
                  (.trans
                    (.comm_mul_left w158 w159 w210)
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w156 w157 w210)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w153 w155 w210)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w149 w152 w210)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_left w146 w148 w210)
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.comm_mul_right w146 w1 w31)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w211)
                        (.comm
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w2)
                        )
                        )
                        (.refl w1)
                        )
                        )
                        (.one_mul w212)
                        )
                        (.deep w213)
                        )
                        (.mul_one w212)
                        )
                        )
                        (.deep w215)
                        )
                        (.mul_one w212)
                        )
                        (.trans
                        (.comm_mul_right w148 w1 w31)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w216)
                        (.comm
                        (.sq
                        (.comm
                        (.sq
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        )
                        (.refl w1)
                        )
                        )
                        (.one_mul w217)
                        )
                        (.deep w218)
                        )
                        (.mul_one w217)
                        )
                        )
                        )
                        )
                        (.deep w220)
                        )
                        (.mul_one w221)
                        )
                        (.trans
                        (.comm_mul_right w152 w1 w31)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w222)
                        (.comm
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        )
                        (.refl w1)
                        )
                        )
                        (.one_mul w223)
                        )
                        (.deep w224)
                        )
                        (.mul_one w223)
                        )
                        )
                        )
                        )
                        (.deep w226)
                        )
                        (.mul_one w227)
                        )
                        (.trans
                        (.comm_mul_right w155 w1 w31)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w228)
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w2)
                        )
                        (.refl w1)
                        )
                        )
                        (.one_mul w229)
                        )
                        (.deep w230)
                        )
                        (.mul_one w229)
                        )
                        )
                        )
                        )
                        (.deep w232)
                        )
                        (.mul_one w233)
                        )
                        (.trans
                        (.comm_mul_right w157 w1 w31)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w234)
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        )
                        (.one_mul w235)
                        )
                        (.deep w236)
                        )
                        (.mul_one w235)
                        )
                        )
                        )
                        )
                        (.deep w238)
                        )
                        (.mul_one w239)
                      )
                      (.trans
                        (.comm_mul_right w159 w1 w31)
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.deep w240)
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        )
                        (.one_mul w241)
                        )
                        (.deep w242)
                        )
                        (.mul_one w241)
                        )
                      )
                    )
                  )
                  (.deep w244)
                )
                (.mul_one w245)
              )
              (.trans
                (.comm_mul_right w162 w1 w31)
                (.trans
                  (.mul
                    (.trans
                      (.mul
                        (.deep w246)
                        (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                      )
                      (.one_mul w247)
                    )
                    (.deep w248)
                  )
                  (.mul_one w247)
                )
              )
            )
          )
        )
        (.trans
          (.comm_mul_left w249 w159 w250)
          (.mul
            (.trans
              (.mul
                (.trans
                  (.comm_mul_right w249 w0 w75)
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.deep w251)
                        (.comm
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        )
                        (.refl w0)
                        )
                        )
                        (.one_mul w252)
                      )
                      (.deep w253)
                    )
                    (.mul_one w252)
                  )
                )
                (.deep w255)
              )
              (.mul_one w252)
            )
            (.trans
              (.comm_mul_right w159 w0 w75)
              (.trans
                (.mul
                  (.trans
                    (.mul
                      (.deep w256)
                      (.comm
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                        (.refl w0)
                      )
                    )
                    (.one_mul w257)
                  )
                  (.deep w258)
                )
                (.mul_one w257)
              )
            )
          )
        )
      )
      (.trans
        (.comm_mul_right w2 w261 w162)
        (.trans
          (.mul
            (.mul
              (.comm
                (.refl w2)
                (.comm
                  (.comm
                    (.comm
                      (.refl w1)
                      (.refl w0)
                    )
                    (.refl w0)
                  )
                  (.refl w1)
                )
              )
              (.trans
                (.comm_mul_right w2 w260 w157)
                (.trans
                  (.mul
                    (.mul
                      (.comm
                        (.refl w2)
                        (.comm
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        (.refl w1)
                        )
                      )
                      (.trans
                        (.comm_mul_right w2 w259 w249)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w0)
                        )
                        (.refl w1)
                        )
                        )
                        )
                        (.trans
                        (.comm_mul_right w2 w84 w152)
                        (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w2)
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w2)
                        (.sq
                        (.sq
                        (.sq
                        (.refl w1)
                        )
                        )
                        )
                        )
                        )
                        (.deep w263)
                        )
                        (.mul_one w265)
                        )
                        )
                        )
                        (.deep w267)
                        )
                        (.mul_one w269)
                        )
                      )
                    )
                    (.deep w271)
                  )
                  (.mul_one w273)
                )
              )
            )
            (.deep w275)
          )
          (.mul_one w277)
        )
      )
    )
    (.trans
      (.comm_mul_right w54 w283 w284)
      (.trans
        (.mul
          (.mul
            (.comm
              (.refl w54)
              (.comm
                (.comm
                  (.comm
                    (.refl w1)
                    (.refl w54)
                  )
                  (.refl w54)
                )
                (.refl w1)
              )
            )
            (.trans
              (.comm_mul_right w54 w280 w282)
              (.trans
                (.mul
                  (.mul
                    (.comm
                      (.refl w54)
                      (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w54)
                        )
                      )
                    )
                    (.trans
                      (.comm_mul_right w54 w279 w152)
                      (.trans
                        (.mul
                        (.mul
                        (.comm
                        (.refl w54)
                        (.sq
                        (.comm
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        (.refl w1)
                        )
                        )
                        )
                        (.comm
                        (.refl w54)
                        (.sq
                        (.sq
                        (.comm
                        (.refl w1)
                        (.refl w54)
                        )
                        )
                        )
                        )
                        )
                        (.deep w286)
                        )
                        (.mul_one w288)
                      )
                    )
                  )
                  (.deep w290)
                )
                (.mul_one w292)
              )
            )
          )
          (.deep w294)
        )
        (.mul_one w296)
      )
    )
  )
)

private theorem trace0_checked : trace0.check = true := by decide

private theorem trace0_sound :
    eval dmModel.val trace0.lhs = eval dmModel.val trace0.rhs :=
  Deriv.sound dmModel trace0 trace0_checked

private def trace1 : Deriv :=
  (.mul
  (.trans
    (.mul
      (.trans
        (.mul
          (.trans
            (.mul
              (.trans
                (.mul
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.mul
                        (.refl w82)
                        (.refl w15)
                        )
                        (.mul
                        (.refl w85)
                        (.refl w9)
                        )
                        )
                        (.trans
                        (.assoc w82 w15 w86)
                        (.mul
                        (.refl w82)
                        (.refl w297)
                        )
                        )
                      )
                      (.mul
                        (.refl w14)
                        (.refl w88)
                      )
                    )
                    (.trans
                      (.assoc w82 w297 w89)
                      (.mul
                        (.refl w82)
                        (.trans
                        (.assoc w15 w86 w89)
                        (.mul
                        (.refl w15)
                        (.trans
                        (.assoc w85 w9 w89)
                        (.mul
                        (.refl w85)
                        (.refl w298)
                        )
                        )
                        )
                        )
                      )
                    )
                  )
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w9)
                        (.refl w17)
                        )
                        (.refl w46)
                        )
                        (.trans
                        (.assoc w9 w17 w46)
                        (.mul
                        (.refl w9)
                        (.refl w299)
                        )
                        )
                        )
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w11)
                        (.refl w25)
                        )
                        (.refl w27)
                        )
                        (.trans
                        (.assoc w11 w25 w27)
                        (.mul
                        (.refl w11)
                        (.refl w300)
                        )
                        )
                        )
                        (.mul
                        (.refl w29)
                        (.refl w27)
                        )
                        )
                        (.trans
                        (.assoc w11 w300 w30)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w25 w27 w30)
                        (.mul
                        (.refl w25)
                        (.refl w301)
                        )
                        )
                        )
                        )
                        )
                        )
                        (.trans
                        (.assoc w9 w299 w303)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w17 w46 w303)
                        (.mul
                        (.refl w17)
                        (.refl w304)
                        )
                        )
                        )
                        )
                      )
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w11)
                        (.refl w42)
                        )
                        (.refl w45)
                        )
                        (.trans
                        (.assoc w11 w42 w45)
                        (.mul
                        (.refl w11)
                        (.refl w305)
                        )
                        )
                        )
                        (.refl w48)
                        )
                        (.trans
                        (.assoc w11 w305 w48)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w42 w45 w48)
                        (.mul
                        (.refl w42)
                        (.refl w306)
                        )
                        )
                        )
                        )
                        )
                        (.refl w53)
                        )
                        (.trans
                        (.assoc w11 w307 w53)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w42 w306 w53)
                        (.mul
                        (.refl w42)
                        (.trans
                        (.assoc w45 w48 w53)
                        (.mul
                        (.refl w45)
                        (.refl w308)
                        )
                        )
                        )
                        )
                        )
                        )
                      )
                    )
                    (.trans
                      (.assoc w9 w309 w312)
                      (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w17 w304 w312)
                        (.mul
                        (.refl w17)
                        (.trans
                        (.assoc w46 w303 w312)
                        (.mul
                        (.refl w46)
                        (.trans
                        (.assoc w11 w302 w312)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w25 w301 w312)
                        (.mul
                        (.refl w25)
                        (.trans
                        (.assoc w27 w30 w312)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w29 w27 w312)
                        (.mul
                        (.refl w29)
                        (.refl w313)
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
                (.trans
                  (.assoc w82 w315 w322)
                  (.mul
                    (.refl w82)
                    (.trans
                      (.assoc w15 w314 w322)
                      (.mul
                        (.refl w15)
                        (.trans
                        (.assoc w85 w298 w322)
                        (.mul
                        (.refl w85)
                        (.trans
                        (.assoc w9 w89 w322)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w14 w88 w322)
                        (.mul
                        (.refl w14)
                        (.refl w323)
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
              (.trans
                (.mul
                  (.mul
                    (.refl w84)
                    (.refl w324)
                  )
                  (.trans
                    (.mul
                      (.mul
                        (.refl w58)
                        (.refl w59)
                      )
                      (.refl w326)
                    )
                    (.trans
                      (.assoc w58 w59 w326)
                      (.mul
                        (.refl w58)
                        (.refl w327)
                      )
                    )
                  )
                )
                (.trans
                  (.assoc w84 w324 w328)
                  (.mul
                    (.refl w84)
                    (.refl w329)
                  )
                )
              )
            )
            (.trans
              (.assoc w82 w333 w334)
              (.mul
                (.refl w82)
                (.trans
                  (.assoc w15 w332 w334)
                  (.mul
                    (.refl w15)
                    (.trans
                      (.assoc w85 w331 w334)
                      (.mul
                        (.refl w85)
                        (.trans
                        (.assoc w9 w330 w334)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w14 w323 w334)
                        (.mul
                        (.refl w14)
                        (.trans
                        (.assoc w88 w322 w334)
                        (.mul
                        (.refl w88)
                        (.trans
                        (.assoc w9 w321 w334)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w17 w320 w334)
                        (.mul
                        (.refl w17)
                        (.trans
                        (.assoc w46 w319 w334)
                        (.mul
                        (.refl w46)
                        (.trans
                        (.assoc w11 w318 w334)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w25 w317 w334)
                        (.mul
                        (.refl w25)
                        (.trans
                        (.assoc w27 w316 w334)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w29 w313 w334)
                        (.mul
                        (.refl w29)
                        (.trans
                        (.assoc w27 w312 w334)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w11 w311 w334)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w42 w310 w334)
                        (.mul
                        (.refl w42)
                        (.trans
                        (.assoc w45 w308 w334)
                        (.mul
                        (.refl w45)
                        (.trans
                        (.assoc w48 w53 w334)
                        (.mul
                        (.refl w48)
                        (.refl w335)
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
          (.trans
            (.mul
              (.trans
                (.mul
                  (.trans
                    (.mul
                      (.mul
                        (.refl w64)
                        (.refl w62)
                      )
                      (.refl w61)
                    )
                    (.trans
                      (.assoc w64 w62 w61)
                      (.mul
                        (.refl w64)
                        (.refl w336)
                      )
                    )
                  )
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.mul
                        (.refl w68)
                        (.refl w66)
                        )
                        (.refl w337)
                        )
                        (.trans
                        (.assoc w68 w66 w337)
                        (.mul
                        (.refl w68)
                        (.refl w338)
                        )
                        )
                      )
                      (.mul
                        (.refl w73)
                        (.refl w71)
                      )
                    )
                    (.trans
                      (.assoc w68 w338 w74)
                      (.mul
                        (.refl w68)
                        (.trans
                        (.assoc w66 w337 w74)
                        (.mul
                        (.refl w66)
                        (.refl w339)
                        )
                        )
                      )
                    )
                  )
                )
                (.trans
                  (.assoc w64 w336 w341)
                  (.mul
                    (.refl w64)
                    (.trans
                      (.assoc w62 w61 w341)
                      (.mul
                        (.refl w62)
                        (.refl w342)
                      )
                    )
                  )
                )
              )
              (.refl w78)
            )
            (.trans
              (.assoc w64 w343 w78)
              (.mul
                (.refl w64)
                (.trans
                  (.assoc w62 w342 w78)
                  (.mul
                    (.refl w62)
                    (.trans
                      (.assoc w61 w341 w78)
                      (.mul
                        (.refl w61)
                        (.trans
                        (.assoc w68 w340 w78)
                        (.mul
                        (.refl w68)
                        (.trans
                        (.assoc w66 w339 w78)
                        (.mul
                        (.refl w66)
                        (.trans
                        (.assoc w337 w74 w78)
                        (.mul
                        (.refl w337)
                        (.trans
                        (.assoc w73 w71 w78)
                        (.mul
                        (.refl w73)
                        (.refl w344)
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
        (.trans
          (.assoc w82 w361 w368)
          (.mul
            (.refl w82)
            (.trans
              (.assoc w15 w360 w368)
              (.mul
                (.refl w15)
                (.trans
                  (.assoc w85 w359 w368)
                  (.mul
                    (.refl w85)
                    (.trans
                      (.assoc w9 w358 w368)
                      (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w14 w357 w368)
                        (.mul
                        (.refl w14)
                        (.trans
                        (.assoc w88 w356 w368)
                        (.mul
                        (.refl w88)
                        (.trans
                        (.assoc w9 w355 w368)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w17 w354 w368)
                        (.mul
                        (.refl w17)
                        (.trans
                        (.assoc w46 w353 w368)
                        (.mul
                        (.refl w46)
                        (.trans
                        (.assoc w11 w352 w368)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w25 w351 w368)
                        (.mul
                        (.refl w25)
                        (.trans
                        (.assoc w27 w350 w368)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w29 w349 w368)
                        (.mul
                        (.refl w29)
                        (.trans
                        (.assoc w27 w348 w368)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w11 w347 w368)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w42 w346 w368)
                        (.mul
                        (.refl w42)
                        (.trans
                        (.assoc w45 w345 w368)
                        (.mul
                        (.refl w45)
                        (.trans
                        (.assoc w48 w335 w368)
                        (.mul
                        (.refl w48)
                        (.trans
                        (.assoc w53 w334 w368)
                        (.mul
                        (.refl w53)
                        (.trans
                        (.assoc w84 w329 w368)
                        (.mul
                        (.refl w84)
                        (.trans
                        (.assoc w324 w328 w368)
                        (.mul
                        (.refl w324)
                        (.trans
                        (.assoc w58 w327 w368)
                        (.mul
                        (.refl w58)
                        (.trans
                        (.assoc w59 w326 w368)
                        (.mul
                        (.refl w59)
                        (.refl w369)
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
      (.trans
        (.mul
          (.trans
            (.mul
              (.mul
                (.refl w98)
                (.refl w94)
              )
              (.mul
                (.refl w107)
                (.refl w103)
              )
            )
            (.trans
              (.assoc w98 w94 w108)
              (.mul
                (.refl w98)
                (.refl w370)
              )
            )
          )
          (.mul
            (.refl w130)
            (.refl w135)
          )
        )
        (.trans
          (.assoc w98 w370 w139)
          (.mul
            (.refl w98)
            (.trans
              (.assoc w94 w108 w139)
              (.mul
                (.refl w94)
                (.trans
                  (.assoc w107 w103 w139)
                  (.mul
                    (.refl w107)
                    (.refl w371)
                  )
                )
              )
            )
          )
        )
      )
    )
    (.trans
      (.assoc w82 w393 w396)
      (.mul
        (.refl w82)
        (.trans
          (.assoc w15 w392 w396)
          (.mul
            (.refl w15)
            (.trans
              (.assoc w85 w391 w396)
              (.mul
                (.refl w85)
                (.trans
                  (.assoc w9 w390 w396)
                  (.mul
                    (.refl w9)
                    (.trans
                      (.assoc w14 w389 w396)
                      (.mul
                        (.refl w14)
                        (.trans
                        (.assoc w88 w388 w396)
                        (.mul
                        (.refl w88)
                        (.trans
                        (.assoc w9 w387 w396)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w17 w386 w396)
                        (.mul
                        (.refl w17)
                        (.trans
                        (.assoc w46 w385 w396)
                        (.mul
                        (.refl w46)
                        (.trans
                        (.assoc w11 w384 w396)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w25 w383 w396)
                        (.mul
                        (.refl w25)
                        (.trans
                        (.assoc w27 w382 w396)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w29 w381 w396)
                        (.mul
                        (.refl w29)
                        (.trans
                        (.assoc w27 w380 w396)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w11 w379 w396)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w42 w378 w396)
                        (.mul
                        (.refl w42)
                        (.trans
                        (.assoc w45 w377 w396)
                        (.mul
                        (.refl w45)
                        (.trans
                        (.assoc w48 w376 w396)
                        (.mul
                        (.refl w48)
                        (.trans
                        (.assoc w53 w375 w396)
                        (.mul
                        (.refl w53)
                        (.trans
                        (.assoc w84 w374 w396)
                        (.mul
                        (.refl w84)
                        (.trans
                        (.assoc w324 w373 w396)
                        (.mul
                        (.refl w324)
                        (.trans
                        (.assoc w58 w372 w396)
                        (.mul
                        (.refl w58)
                        (.trans
                        (.assoc w59 w369 w396)
                        (.mul
                        (.refl w59)
                        (.trans
                        (.assoc w326 w368 w396)
                        (.mul
                        (.refl w326)
                        (.trans
                        (.assoc w64 w367 w396)
                        (.mul
                        (.refl w64)
                        (.trans
                        (.assoc w62 w366 w396)
                        (.mul
                        (.refl w62)
                        (.trans
                        (.assoc w61 w365 w396)
                        (.mul
                        (.refl w61)
                        (.trans
                        (.assoc w68 w364 w396)
                        (.mul
                        (.refl w68)
                        (.trans
                        (.assoc w66 w363 w396)
                        (.mul
                        (.refl w66)
                        (.trans
                        (.assoc w337 w362 w396)
                        (.mul
                        (.refl w337)
                        (.trans
                        (.assoc w73 w344 w396)
                        (.mul
                        (.refl w73)
                        (.trans
                        (.assoc w71 w78 w396)
                        (.mul
                        (.refl w71)
                        (.refl w397)
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
  (.trans
    (.mul
      (.trans
        (.mul
          (.trans
            (.mul
              (.trans
                (.mul
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w164)
                        (.refl w165)
                        )
                        (.refl w169)
                        )
                        (.trans
                        (.assoc w164 w165 w169)
                        (.mul
                        (.refl w164)
                        (.refl w398)
                        )
                        )
                        )
                        (.refl w173)
                        )
                        (.trans
                        (.assoc w164 w398 w173)
                        (.mul
                        (.refl w164)
                        (.trans
                        (.assoc w165 w169 w173)
                        (.mul
                        (.refl w165)
                        (.refl w399)
                        )
                        )
                        )
                        )
                        )
                        (.refl w177)
                        )
                        (.trans
                        (.assoc w164 w400 w177)
                        (.mul
                        (.refl w164)
                        (.trans
                        (.assoc w165 w399 w177)
                        (.mul
                        (.refl w165)
                        (.trans
                        (.assoc w169 w173 w177)
                        (.mul
                        (.refl w169)
                        (.refl w401)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.refl w181)
                        )
                        (.trans
                        (.assoc w164 w403 w181)
                        (.mul
                        (.refl w164)
                        (.trans
                        (.assoc w165 w402 w181)
                        (.mul
                        (.refl w165)
                        (.trans
                        (.assoc w169 w401 w181)
                        (.mul
                        (.refl w169)
                        (.trans
                        (.assoc w173 w177 w181)
                        (.mul
                        (.refl w173)
                        (.refl w404)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.refl w185)
                        )
                        (.trans
                        (.assoc w164 w407 w185)
                        (.mul
                        (.refl w164)
                        (.trans
                        (.assoc w165 w406 w185)
                        (.mul
                        (.refl w165)
                        (.trans
                        (.assoc w169 w405 w185)
                        (.mul
                        (.refl w169)
                        (.trans
                        (.assoc w173 w404 w185)
                        (.mul
                        (.refl w173)
                        (.trans
                        (.assoc w177 w181 w185)
                        (.mul
                        (.refl w177)
                        (.refl w408)
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
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w188)
                        (.refl w192)
                        )
                        (.refl w196)
                        )
                        (.trans
                        (.assoc w188 w192 w196)
                        (.mul
                        (.refl w188)
                        (.refl w409)
                        )
                        )
                        )
                        (.refl w200)
                        )
                        (.trans
                        (.assoc w188 w409 w200)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w196 w200)
                        (.mul
                        (.refl w192)
                        (.refl w410)
                        )
                        )
                        )
                        )
                        )
                        (.refl w204)
                        )
                        (.trans
                        (.assoc w188 w411 w204)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w410 w204)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w200 w204)
                        (.mul
                        (.refl w196)
                        (.refl w412)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.refl w208)
                        )
                        (.trans
                        (.assoc w188 w414 w208)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w413 w208)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w412 w208)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.assoc w200 w204 w208)
                        (.mul
                        (.refl w200)
                        (.refl w415)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.refl w416)
                        )
                        (.trans
                        (.assoc w188 w419 w416)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w418 w416)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w417 w416)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.assoc w200 w415 w416)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.assoc w204 w208 w416)
                        (.mul
                        (.refl w204)
                        (.refl w420)
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
                    (.trans
                      (.assoc w164 w424 w429)
                      (.mul
                        (.refl w164)
                        (.trans
                        (.assoc w165 w423 w429)
                        (.mul
                        (.refl w165)
                        (.trans
                        (.assoc w169 w422 w429)
                        (.mul
                        (.refl w169)
                        (.trans
                        (.assoc w173 w421 w429)
                        (.mul
                        (.refl w173)
                        (.trans
                        (.assoc w177 w408 w429)
                        (.mul
                        (.refl w177)
                        (.trans
                        (.assoc w181 w185 w429)
                        (.mul
                        (.refl w181)
                        (.refl w430)
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
                  (.trans
                    (.mul
                      (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w212)
                        (.refl w217)
                        )
                        (.refl w223)
                        )
                        (.trans
                        (.assoc w212 w217 w223)
                        (.mul
                        (.refl w212)
                        (.refl w431)
                        )
                        )
                        )
                        (.refl w229)
                        )
                        (.trans
                        (.assoc w212 w431 w229)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w223 w229)
                        (.mul
                        (.refl w217)
                        (.refl w432)
                        )
                        )
                        )
                        )
                        )
                        (.refl w235)
                        )
                        (.trans
                        (.assoc w212 w433 w235)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w432 w235)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.assoc w223 w229 w235)
                        (.mul
                        (.refl w223)
                        (.refl w434)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        (.refl w241)
                        )
                        (.trans
                        (.assoc w212 w436 w241)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w435 w241)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.assoc w223 w434 w241)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.assoc w229 w235 w241)
                        (.mul
                        (.refl w229)
                        (.refl w437)
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                        )
                      )
                      (.refl w247)
                    )
                    (.trans
                      (.assoc w212 w440 w247)
                      (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w439 w247)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.assoc w223 w438 w247)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.assoc w229 w437 w247)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.assoc w235 w241 w247)
                        (.mul
                        (.refl w235)
                        (.refl w441)
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
                (.trans
                  (.assoc w164 w446 w451)
                  (.mul
                    (.refl w164)
                    (.trans
                      (.assoc w165 w445 w451)
                      (.mul
                        (.refl w165)
                        (.trans
                        (.assoc w169 w444 w451)
                        (.mul
                        (.refl w169)
                        (.trans
                        (.assoc w173 w443 w451)
                        (.mul
                        (.refl w173)
                        (.trans
                        (.assoc w177 w442 w451)
                        (.mul
                        (.refl w177)
                        (.trans
                        (.assoc w181 w430 w451)
                        (.mul
                        (.refl w181)
                        (.trans
                        (.assoc w185 w429 w451)
                        (.mul
                        (.refl w185)
                        (.trans
                        (.assoc w188 w428 w451)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w427 w451)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w426 w451)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.assoc w200 w425 w451)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.assoc w204 w420 w451)
                        (.mul
                        (.refl w204)
                        (.trans
                        (.assoc w208 w416 w451)
                        (.mul
                        (.refl w208)
                        (.refl w452)
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
              (.mul
                (.refl w252)
                (.refl w257)
              )
            )
            (.trans
              (.assoc w164 w464 w465)
              (.mul
                (.refl w164)
                (.trans
                  (.assoc w165 w463 w465)
                  (.mul
                    (.refl w165)
                    (.trans
                      (.assoc w169 w462 w465)
                      (.mul
                        (.refl w169)
                        (.trans
                        (.assoc w173 w461 w465)
                        (.mul
                        (.refl w173)
                        (.trans
                        (.assoc w177 w460 w465)
                        (.mul
                        (.refl w177)
                        (.trans
                        (.assoc w181 w459 w465)
                        (.mul
                        (.refl w181)
                        (.trans
                        (.assoc w185 w458 w465)
                        (.mul
                        (.refl w185)
                        (.trans
                        (.assoc w188 w457 w465)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w456 w465)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w455 w465)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.assoc w200 w454 w465)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.assoc w204 w453 w465)
                        (.mul
                        (.refl w204)
                        (.trans
                        (.assoc w208 w452 w465)
                        (.mul
                        (.refl w208)
                        (.trans
                        (.assoc w416 w451 w465)
                        (.mul
                        (.refl w416)
                        (.trans
                        (.assoc w212 w450 w465)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w449 w465)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.assoc w223 w448 w465)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.assoc w229 w447 w465)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.assoc w235 w441 w465)
                        (.mul
                        (.refl w235)
                        (.trans
                        (.assoc w241 w247 w465)
                        (.mul
                        (.refl w241)
                        (.refl w466)
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
          (.mul
            (.refl w276)
            (.mul
              (.refl w272)
              (.mul
                (.refl w268)
                (.mul
                  (.refl w264)
                  (.refl w262)
                )
              )
            )
          )
        )
        (.trans
          (.assoc w164 w485 w277)
          (.mul
            (.refl w164)
            (.trans
              (.assoc w165 w484 w277)
              (.mul
                (.refl w165)
                (.trans
                  (.assoc w169 w483 w277)
                  (.mul
                    (.refl w169)
                    (.trans
                      (.assoc w173 w482 w277)
                      (.mul
                        (.refl w173)
                        (.trans
                        (.assoc w177 w481 w277)
                        (.mul
                        (.refl w177)
                        (.trans
                        (.assoc w181 w480 w277)
                        (.mul
                        (.refl w181)
                        (.trans
                        (.assoc w185 w479 w277)
                        (.mul
                        (.refl w185)
                        (.trans
                        (.assoc w188 w478 w277)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w477 w277)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w476 w277)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.assoc w200 w475 w277)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.assoc w204 w474 w277)
                        (.mul
                        (.refl w204)
                        (.trans
                        (.assoc w208 w473 w277)
                        (.mul
                        (.refl w208)
                        (.trans
                        (.assoc w416 w472 w277)
                        (.mul
                        (.refl w416)
                        (.trans
                        (.assoc w212 w471 w277)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w470 w277)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.assoc w223 w469 w277)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.assoc w229 w468 w277)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.assoc w235 w467 w277)
                        (.mul
                        (.refl w235)
                        (.trans
                        (.assoc w241 w466 w277)
                        (.mul
                        (.refl w241)
                        (.trans
                        (.assoc w247 w465 w277)
                        (.mul
                        (.refl w247)
                        (.trans
                        (.assoc w252 w257 w277)
                        (.mul
                        (.refl w252)
                        (.refl w486)
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
      (.mul
        (.refl w295)
        (.mul
          (.refl w291)
          (.mul
            (.refl w287)
            (.refl w285)
          )
        )
      )
    )
    (.trans
      (.assoc w164 w507 w296)
      (.mul
        (.refl w164)
        (.trans
          (.assoc w165 w506 w296)
          (.mul
            (.refl w165)
            (.trans
              (.assoc w169 w505 w296)
              (.mul
                (.refl w169)
                (.trans
                  (.assoc w173 w504 w296)
                  (.mul
                    (.refl w173)
                    (.trans
                      (.assoc w177 w503 w296)
                      (.mul
                        (.refl w177)
                        (.trans
                        (.assoc w181 w502 w296)
                        (.mul
                        (.refl w181)
                        (.trans
                        (.assoc w185 w501 w296)
                        (.mul
                        (.refl w185)
                        (.trans
                        (.assoc w188 w500 w296)
                        (.mul
                        (.refl w188)
                        (.trans
                        (.assoc w192 w499 w296)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.assoc w196 w498 w296)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.assoc w200 w497 w296)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.assoc w204 w496 w296)
                        (.mul
                        (.refl w204)
                        (.trans
                        (.assoc w208 w495 w296)
                        (.mul
                        (.refl w208)
                        (.trans
                        (.assoc w416 w494 w296)
                        (.mul
                        (.refl w416)
                        (.trans
                        (.assoc w212 w493 w296)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.assoc w217 w492 w296)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.assoc w223 w491 w296)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.assoc w229 w490 w296)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.assoc w235 w489 w296)
                        (.mul
                        (.refl w235)
                        (.trans
                        (.assoc w241 w488 w296)
                        (.mul
                        (.refl w241)
                        (.trans
                        (.assoc w247 w487 w296)
                        (.mul
                        (.refl w247)
                        (.trans
                        (.assoc w252 w486 w296)
                        (.mul
                        (.refl w252)
                        (.trans
                        (.assoc w257 w277 w296)
                        (.mul
                        (.refl w257)
                        (.trans
                        (.assoc w276 w273 w296)
                        (.mul
                        (.refl w276)
                        (.trans
                        (.assoc w272 w269 w296)
                        (.mul
                        (.refl w272)
                        (.trans
                        (.assoc w268 w265 w296)
                        (.mul
                        (.refl w268)
                        (.trans
                        (.assoc w264 w262 w296)
                        (.mul
                        (.refl w264)
                        (.refl w508)
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

private theorem trace1_checked : trace1.check = true := by decide

private theorem trace1_sound :
    eval dmModel.val trace1.lhs = eval dmModel.val trace1.rhs :=
  Deriv.sound dmModel trace1 trace1_checked

private def trace2 : Deriv :=
  (.assoc w82 w539 w566)

private theorem trace2_checked : trace2.check = true := by decide

private theorem trace2_sound :
    eval dmModel.val trace2.lhs = eval dmModel.val trace2.rhs :=
  Deriv.sound dmModel trace2 trace2_checked

private def trace3 : Deriv :=
  (.mul
  (.refl w82)
  (.trans
    (.assoc w15 w538 w566)
    (.mul
      (.refl w15)
      (.trans
        (.assoc w85 w537 w566)
        (.mul
          (.refl w85)
          (.trans
            (.assoc w9 w536 w566)
            (.mul
              (.refl w9)
              (.trans
                (.assoc w14 w535 w566)
                (.mul
                  (.refl w14)
                  (.trans
                    (.assoc w88 w534 w566)
                    (.mul
                      (.refl w88)
                      (.trans
                        (.assoc w9 w533 w566)
                        (.mul
                        (.refl w9)
                        (.trans
                        (.assoc w17 w532 w566)
                        (.mul
                        (.refl w17)
                        (.trans
                        (.assoc w46 w531 w566)
                        (.mul
                        (.refl w46)
                        (.trans
                        (.assoc w11 w530 w566)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w25 w529 w566)
                        (.mul
                        (.refl w25)
                        (.trans
                        (.assoc w27 w528 w566)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w29 w527 w566)
                        (.mul
                        (.refl w29)
                        (.trans
                        (.assoc w27 w526 w566)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.assoc w11 w525 w566)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.assoc w42 w524 w566)
                        (.mul
                        (.refl w42)
                        (.trans
                        (.assoc w45 w523 w566)
                        (.mul
                        (.refl w45)
                        (.trans
                        (.assoc w48 w522 w566)
                        (.mul
                        (.refl w48)
                        (.trans
                        (.assoc w53 w521 w566)
                        (.mul
                        (.refl w53)
                        (.trans
                        (.assoc w84 w520 w566)
                        (.mul
                        (.refl w84)
                        (.trans
                        (.assoc w324 w519 w566)
                        (.mul
                        (.refl w324)
                        (.trans
                        (.assoc w58 w518 w566)
                        (.mul
                        (.refl w58)
                        (.trans
                        (.assoc w59 w517 w566)
                        (.mul
                        (.refl w59)
                        (.trans
                        (.assoc w326 w516 w566)
                        (.mul
                        (.refl w326)
                        (.trans
                        (.assoc w64 w515 w566)
                        (.mul
                        (.refl w64)
                        (.trans
                        (.assoc w62 w514 w566)
                        (.mul
                        (.refl w62)
                        (.trans
                        (.assoc w61 w513 w566)
                        (.mul
                        (.refl w61)
                        (.trans
                        (.assoc w68 w512 w566)
                        (.mul
                        (.refl w68)
                        (.trans
                        (.assoc w66 w511 w566)
                        (.mul
                        (.refl w66)
                        (.trans
                        (.assoc w337 w510 w566)
                        (.mul
                        (.refl w337)
                        (.trans
                        (.assoc w73 w509 w566)
                        (.mul
                        (.refl w73)
                        (.trans
                        (.assoc w71 w397 w566)
                        (.mul
                        (.refl w71)
                        (.trans
                        (.assoc w78 w396 w566)
                        (.mul
                        (.refl w78)
                        (.trans
                        (.assoc w98 w395 w566)
                        (.mul
                        (.refl w98)
                        (.trans
                        (.assoc w94 w394 w566)
                        (.mul
                        (.refl w94)
                        (.trans
                        (.assoc w107 w371 w566)
                        (.mul
                        (.refl w107)
                        (.trans
                        (.assoc w103 w139 w566)
                        (.mul
                        (.refl w103)
                        (.trans
                        (.assoc w130 w135 w566)
                        (.mul
                        (.refl w130)
                        (.refl w567)
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

private theorem trace3_checked : trace3.check = true := by decide

private theorem trace3_sound :
    eval dmModel.val trace3.lhs = eval dmModel.val trace3.rhs :=
  Deriv.sound dmModel trace3 trace3_checked

private def trace4 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.mul
                        (.refl w29)
                        (.mul
                        (.refl w27)
                        (.mul
                        (.refl w11)
                        (.mul
                        (.refl w42)
                        (.mul
                        (.refl w45)
                        (.mul
                        (.refl w48)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w53 w84 w585)
                        )
                        (.mul
                        (.swap w53 w84)
                        (.refl w585)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w53)
                        )
                        (.deep w586)
                        )
                        (.mul_one w587)
                        )
                        (.refl w585)
                        )
                        )
                        (.assoc w84 w53 w585)
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

private theorem trace4_checked : trace4.check = true := by decide

private theorem trace4_sound :
    eval dmModel.val trace4.lhs = eval dmModel.val trace4.rhs :=
  Deriv.sound dmModel trace4 trace4_checked

private def trace5 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.mul
                        (.refl w29)
                        (.mul
                        (.refl w27)
                        (.mul
                        (.refl w11)
                        (.mul
                        (.refl w42)
                        (.mul
                        (.refl w45)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w48 w84 w588)
                        )
                        (.mul
                        (.swap w48 w84)
                        (.refl w588)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w48)
                        )
                        (.deep w589)
                        )
                        (.mul_one w590)
                        )
                        (.refl w588)
                        )
                        )
                        (.assoc w84 w48 w588)
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

private theorem trace5_checked : trace5.check = true := by decide

private theorem trace5_sound :
    eval dmModel.val trace5.lhs = eval dmModel.val trace5.rhs :=
  Deriv.sound dmModel trace5 trace5_checked

private def trace6 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.mul
                        (.refl w29)
                        (.mul
                        (.refl w27)
                        (.mul
                        (.refl w11)
                        (.mul
                        (.refl w42)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w45 w84 w591)
                        )
                        (.mul
                        (.swap w45 w84)
                        (.refl w591)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w45)
                        )
                        (.deep w592)
                        )
                        (.mul_one w593)
                        )
                        (.refl w591)
                        )
                        )
                        (.assoc w84 w45 w591)
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

private theorem trace6_checked : trace6.check = true := by decide

private theorem trace6_sound :
    eval dmModel.val trace6.lhs = eval dmModel.val trace6.rhs :=
  Deriv.sound dmModel trace6 trace6_checked

private def trace7 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.mul
                        (.refl w29)
                        (.mul
                        (.refl w27)
                        (.mul
                        (.refl w11)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w42 w84 w594)
                        )
                        (.mul
                        (.swap w42 w84)
                        (.refl w594)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w42)
                        )
                        (.deep w595)
                        )
                        (.mul_one w596)
                        )
                        (.refl w594)
                        )
                        )
                        (.assoc w84 w42 w594)
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

private theorem trace7_checked : trace7.check = true := by decide

private theorem trace7_sound :
    eval dmModel.val trace7.lhs = eval dmModel.val trace7.rhs :=
  Deriv.sound dmModel trace7 trace7_checked

private def trace8 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.mul
                        (.refl w29)
                        (.mul
                        (.refl w27)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w11 w84 w597)
                        )
                        (.mul
                        (.swap w11 w84)
                        (.refl w597)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w11)
                        )
                        (.deep w598)
                        )
                        (.mul_one w599)
                        )
                        (.refl w597)
                        )
                        )
                        (.assoc w84 w11 w597)
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

private theorem trace8_checked : trace8.check = true := by decide

private theorem trace8_sound :
    eval dmModel.val trace8.lhs = eval dmModel.val trace8.rhs :=
  Deriv.sound dmModel trace8 trace8_checked

private def trace9 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.mul
                        (.refl w29)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w27 w84 w600)
                        )
                        (.mul
                        (.swap w27 w84)
                        (.refl w600)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w27)
                        )
                        (.deep w601)
                        )
                        (.mul_one w602)
                        )
                        (.refl w600)
                        )
                        )
                        (.assoc w84 w27 w600)
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

private theorem trace9_checked : trace9.check = true := by decide

private theorem trace9_sound :
    eval dmModel.val trace9.lhs = eval dmModel.val trace9.rhs :=
  Deriv.sound dmModel trace9 trace9_checked

private def trace10 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.mul
                        (.refl w27)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w29 w84 w603)
                        )
                        (.mul
                        (.swap w29 w84)
                        (.refl w603)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w29)
                        )
                        (.deep w604)
                        )
                        (.mul_one w605)
                        )
                        (.refl w603)
                        )
                        )
                        (.assoc w84 w29 w603)
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

private theorem trace10_checked : trace10.check = true := by decide

private theorem trace10_sound :
    eval dmModel.val trace10.lhs = eval dmModel.val trace10.rhs :=
  Deriv.sound dmModel trace10 trace10_checked

private def trace11 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w25)
                      (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w27 w84 w606)
                        )
                        (.mul
                        (.swap w27 w84)
                        (.refl w606)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w27)
                        )
                        (.deep w601)
                        )
                        (.mul_one w602)
                        )
                        (.refl w606)
                        )
                        )
                        (.assoc w84 w27 w606)
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

private theorem trace11_checked : trace11.check = true := by decide

private theorem trace11_sound :
    eval dmModel.val trace11.lhs = eval dmModel.val trace11.rhs :=
  Deriv.sound dmModel trace11 trace11_checked

private def trace12 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.mul
                    (.refl w11)
                    (.trans
                      (.trans
                        (.trans
                        (.symm
                        (.assoc w25 w84 w607)
                        )
                        (.mul
                        (.swap w25 w84)
                        (.refl w607)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w25)
                        )
                        (.deep w608)
                        )
                        (.mul_one w609)
                        )
                        (.refl w607)
                        )
                      )
                      (.assoc w84 w25 w607)
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

private theorem trace12_checked : trace12.check = true := by decide

private theorem trace12_sound :
    eval dmModel.val trace12.lhs = eval dmModel.val trace12.rhs :=
  Deriv.sound dmModel trace12 trace12_checked

private def trace13 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.mul
                  (.refl w46)
                  (.trans
                    (.trans
                      (.trans
                        (.symm
                        (.assoc w11 w84 w610)
                        )
                        (.mul
                        (.swap w11 w84)
                        (.refl w610)
                        )
                      )
                      (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w11)
                        )
                        (.deep w598)
                        )
                        (.mul_one w599)
                        )
                        (.refl w610)
                      )
                    )
                    (.assoc w84 w11 w610)
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

private theorem trace13_checked : trace13.check = true := by decide

private theorem trace13_sound :
    eval dmModel.val trace13.lhs = eval dmModel.val trace13.rhs :=
  Deriv.sound dmModel trace13 trace13_checked

private def trace14 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.mul
                (.refl w17)
                (.trans
                  (.trans
                    (.trans
                      (.symm
                        (.assoc w46 w84 w611)
                      )
                      (.mul
                        (.swap w46 w84)
                        (.refl w611)
                      )
                    )
                    (.mul
                      (.trans
                        (.mul
                        (.mul
                        (.refl w84)
                        (.refl w46)
                        )
                        (.deep w612)
                        )
                        (.mul_one w613)
                      )
                      (.refl w611)
                    )
                  )
                  (.assoc w84 w46 w611)
                )
              )
            )
          )
        )
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
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.mul
              (.refl w9)
              (.trans
                (.trans
                  (.trans
                    (.symm
                      (.assoc w17 w84 w614)
                    )
                    (.mul
                      (.swap w17 w84)
                      (.refl w614)
                    )
                  )
                  (.mul
                    (.trans
                      (.mul
                        (.mul
                        (.refl w84)
                        (.refl w17)
                        )
                        (.deep w615)
                      )
                      (.mul_one w616)
                    )
                    (.refl w614)
                  )
                )
                (.assoc w84 w17 w614)
              )
            )
          )
        )
      )
    )
  )
)

private theorem trace15_checked : trace15.check = true := by decide

private theorem trace15_sound :
    eval dmModel.val trace15.lhs = eval dmModel.val trace15.rhs :=
  Deriv.sound dmModel trace15 trace15_checked

private def trace16 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.mul
            (.refl w88)
            (.trans
              (.trans
                (.trans
                  (.symm
                    (.assoc w9 w84 w617)
                  )
                  (.mul
                    (.swap w9 w84)
                    (.refl w617)
                  )
                )
                (.mul
                  (.trans
                    (.mul
                      (.mul
                        (.refl w84)
                        (.refl w9)
                      )
                      (.deep w618)
                    )
                    (.mul_one w619)
                  )
                  (.refl w617)
                )
              )
              (.assoc w84 w9 w617)
            )
          )
        )
      )
    )
  )
)

private theorem trace16_checked : trace16.check = true := by decide

private theorem trace16_sound :
    eval dmModel.val trace16.lhs = eval dmModel.val trace16.rhs :=
  Deriv.sound dmModel trace16 trace16_checked

private def trace17 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.mul
          (.refl w14)
          (.trans
            (.trans
              (.trans
                (.symm
                  (.assoc w88 w84 w620)
                )
                (.mul
                  (.swap w88 w84)
                  (.refl w620)
                )
              )
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.refl w84)
                      (.refl w88)
                    )
                    (.deep w621)
                  )
                  (.mul_one w622)
                )
                (.refl w620)
              )
            )
            (.assoc w84 w88 w620)
          )
        )
      )
    )
  )
)

private theorem trace17_checked : trace17.check = true := by decide

private theorem trace17_sound :
    eval dmModel.val trace17.lhs = eval dmModel.val trace17.rhs :=
  Deriv.sound dmModel trace17 trace17_checked

private def trace18 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.mul
        (.refl w9)
        (.trans
          (.trans
            (.trans
              (.symm
                (.assoc w14 w84 w623)
              )
              (.mul
                (.swap w14 w84)
                (.refl w623)
              )
            )
            (.mul
              (.trans
                (.mul
                  (.mul
                    (.refl w84)
                    (.refl w14)
                  )
                  (.deep w624)
                )
                (.mul_one w625)
              )
              (.refl w623)
            )
          )
          (.assoc w84 w14 w623)
        )
      )
    )
  )
)

private theorem trace18_checked : trace18.check = true := by decide

private theorem trace18_sound :
    eval dmModel.val trace18.lhs = eval dmModel.val trace18.rhs :=
  Deriv.sound dmModel trace18 trace18_checked

private def trace19 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w85)
      (.trans
        (.trans
          (.trans
            (.symm
              (.assoc w9 w84 w626)
            )
            (.mul
              (.swap w9 w84)
              (.refl w626)
            )
          )
          (.mul
            (.trans
              (.mul
                (.mul
                  (.refl w84)
                  (.refl w9)
                )
                (.deep w618)
              )
              (.mul_one w619)
            )
            (.refl w626)
          )
        )
        (.assoc w84 w9 w626)
      )
    )
  )
)

private theorem trace19_checked : trace19.check = true := by decide

private theorem trace19_sound :
    eval dmModel.val trace19.lhs = eval dmModel.val trace19.rhs :=
  Deriv.sound dmModel trace19 trace19_checked

private def trace20 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.trans
      (.trans
        (.symm
          (.assoc w85 w84 w627)
        )
        (.mul
          (.inv_mul w84)
          (.refl w627)
        )
      )
      (.one_mul w627)
    )
  )
)

private theorem trace20_checked : trace20.check = true := by decide

private theorem trace20_sound :
    eval dmModel.val trace20.lhs = eval dmModel.val trace20.rhs :=
  Deriv.sound dmModel trace20 trace20_checked

private def trace21 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w9)
      (.mul
        (.refl w14)
        (.mul
          (.refl w88)
          (.mul
            (.refl w9)
            (.mul
              (.symm
                (.inv_comm w10 w2)
              )
              (.refl w614)
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
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w9)
      (.mul
        (.refl w14)
        (.mul
          (.refl w88)
          (.trans
            (.trans
              (.trans
                (.symm
                  (.assoc w9 w628 w614)
                )
                (.mul
                  (.swap w9 w628)
                  (.refl w614)
                )
              )
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.refl w628)
                      (.refl w9)
                    )
                    (.deep w629)
                  )
                  (.mul_one w630)
                )
                (.refl w614)
              )
            )
            (.assoc w628 w9 w614)
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
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w9)
      (.mul
        (.refl w14)
        (.trans
          (.trans
            (.trans
              (.symm
                (.assoc w88 w628 w631)
              )
              (.mul
                (.swap w88 w628)
                (.refl w631)
              )
            )
            (.mul
              (.trans
                (.mul
                  (.mul
                    (.refl w628)
                    (.refl w88)
                  )
                  (.deep w632)
                )
                (.mul_one w633)
              )
              (.refl w631)
            )
          )
          (.assoc w628 w88 w631)
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
  (.refl w82)
  (.mul
    (.refl w15)
    (.mul
      (.refl w9)
      (.trans
        (.trans
          (.trans
            (.symm
              (.assoc w14 w628 w634)
            )
            (.mul
              (.swap w14 w628)
              (.refl w634)
            )
          )
          (.mul
            (.trans
              (.mul
                (.mul
                  (.refl w628)
                  (.refl w14)
                )
                (.deep w635)
              )
              (.mul_one w636)
            )
            (.refl w634)
          )
        )
        (.assoc w628 w14 w634)
      )
    )
  )
)

private theorem trace24_checked : trace24.check = true := by decide

private theorem trace24_sound :
    eval dmModel.val trace24.lhs = eval dmModel.val trace24.rhs :=
  Deriv.sound dmModel trace24 trace24_checked

private def trace25 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w15)
    (.trans
      (.trans
        (.trans
          (.symm
            (.assoc w9 w628 w637)
          )
          (.mul
            (.swap w9 w628)
            (.refl w637)
          )
        )
        (.mul
          (.trans
            (.mul
              (.mul
                (.refl w628)
                (.refl w9)
              )
              (.deep w629)
            )
            (.mul_one w630)
          )
          (.refl w637)
        )
      )
      (.assoc w628 w9 w637)
    )
  )
)

private theorem trace25_checked : trace25.check = true := by decide

private theorem trace25_sound :
    eval dmModel.val trace25.lhs = eval dmModel.val trace25.rhs :=
  Deriv.sound dmModel trace25 trace25_checked

private def trace26 : Deriv :=
  (.mul
  (.refl w82)
  (.trans
    (.trans
      (.symm
        (.assoc w15 w628 w638)
      )
      (.mul
        (.mul_inv w15)
        (.refl w638)
      )
    )
    (.one_mul w638)
  )
)

private theorem trace26_checked : trace26.check = true := by decide

private theorem trace26_sound :
    eval dmModel.val trace26.lhs = eval dmModel.val trace26.rhs :=
  Deriv.sound dmModel trace26 trace26_checked

private def trace27 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w14)
      (.mul
        (.refl w88)
        (.mul
          (.refl w9)
          (.mul
            (.refl w46)
            (.mul
              (.symm
                (.inv_comm w4 w10)
              )
              (.refl w610)
            )
          )
        )
      )
    )
  )
)

private theorem trace27_checked : trace27.check = true := by decide

private theorem trace27_sound :
    eval dmModel.val trace27.lhs = eval dmModel.val trace27.rhs :=
  Deriv.sound dmModel trace27 trace27_checked

private def trace28 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w14)
      (.mul
        (.refl w88)
        (.mul
          (.refl w9)
          (.trans
            (.trans
              (.trans
                (.symm
                  (.assoc w46 w35 w610)
                )
                (.mul
                  (.swap w46 w35)
                  (.refl w610)
                )
              )
              (.mul
                (.trans
                  (.mul
                    (.mul
                      (.refl w35)
                      (.refl w46)
                    )
                    (.deep w639)
                  )
                  (.mul_one w640)
                )
                (.refl w610)
              )
            )
            (.assoc w35 w46 w610)
          )
        )
      )
    )
  )
)

private theorem trace28_checked : trace28.check = true := by decide

private theorem trace28_sound :
    eval dmModel.val trace28.lhs = eval dmModel.val trace28.rhs :=
  Deriv.sound dmModel trace28 trace28_checked

private def trace29 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w14)
      (.mul
        (.refl w88)
        (.trans
          (.trans
            (.trans
              (.symm
                (.assoc w9 w35 w641)
              )
              (.mul
                (.swap w9 w35)
                (.refl w641)
              )
            )
            (.mul
              (.trans
                (.mul
                  (.mul
                    (.refl w35)
                    (.refl w9)
                  )
                  (.deep w642)
                )
                (.mul_one w643)
              )
              (.refl w641)
            )
          )
          (.assoc w35 w9 w641)
        )
      )
    )
  )
)

private theorem trace29_checked : trace29.check = true := by decide

private theorem trace29_sound :
    eval dmModel.val trace29.lhs = eval dmModel.val trace29.rhs :=
  Deriv.sound dmModel trace29 trace29_checked

private def trace30 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w14)
      (.trans
        (.trans
          (.trans
            (.symm
              (.assoc w88 w35 w644)
            )
            (.mul
              (.swap w88 w35)
              (.refl w644)
            )
          )
          (.mul
            (.trans
              (.mul
                (.mul
                  (.refl w35)
                  (.refl w88)
                )
                (.deep w645)
              )
              (.mul_one w646)
            )
            (.refl w644)
          )
        )
        (.assoc w35 w88 w644)
      )
    )
  )
)

private theorem trace30_checked : trace30.check = true := by decide

private theorem trace30_sound :
    eval dmModel.val trace30.lhs = eval dmModel.val trace30.rhs :=
  Deriv.sound dmModel trace30 trace30_checked

private def trace31 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.trans
      (.trans
        (.symm
          (.assoc w14 w35 w647)
        )
        (.mul
          (.mul_inv w14)
          (.refl w647)
        )
      )
      (.one_mul w647)
    )
  )
)

private theorem trace31_checked : trace31.check = true := by decide

private theorem trace31_sound :
    eval dmModel.val trace31.lhs = eval dmModel.val trace31.rhs :=
  Deriv.sound dmModel trace31 trace31_checked

private def trace32 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w29)
                (.mul
                  (.refl w27)
                  (.mul
                    (.refl w11)
                    (.mul
                      (.refl w42)
                      (.mul
                        (.symm
                        (.inv_comm w26 w4)
                        )
                        (.refl w591)
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

private theorem trace32_checked : trace32.check = true := by decide

private theorem trace32_sound :
    eval dmModel.val trace32.lhs = eval dmModel.val trace32.rhs :=
  Deriv.sound dmModel trace32 trace32_checked

private def trace33 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w29)
                (.mul
                  (.refl w27)
                  (.mul
                    (.refl w11)
                    (.trans
                      (.trans
                        (.trans
                        (.symm
                        (.assoc w42 w43 w591)
                        )
                        (.mul
                        (.swap w42 w43)
                        (.refl w591)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w43)
                        (.refl w42)
                        )
                        (.deep w648)
                        )
                        (.mul_one w649)
                        )
                        (.refl w591)
                        )
                      )
                      (.assoc w43 w42 w591)
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

private theorem trace33_checked : trace33.check = true := by decide

private theorem trace33_sound :
    eval dmModel.val trace33.lhs = eval dmModel.val trace33.rhs :=
  Deriv.sound dmModel trace33 trace33_checked

private def trace34 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w29)
                (.mul
                  (.refl w27)
                  (.trans
                    (.trans
                      (.trans
                        (.symm
                        (.assoc w11 w43 w650)
                        )
                        (.mul
                        (.swap w11 w43)
                        (.refl w650)
                        )
                      )
                      (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w43)
                        (.refl w11)
                        )
                        (.deep w651)
                        )
                        (.mul_one w652)
                        )
                        (.refl w650)
                      )
                    )
                    (.assoc w43 w11 w650)
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

private theorem trace34_checked : trace34.check = true := by decide

private theorem trace34_sound :
    eval dmModel.val trace34.lhs = eval dmModel.val trace34.rhs :=
  Deriv.sound dmModel trace34 trace34_checked

private def trace35 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w29)
                (.trans
                  (.trans
                    (.trans
                      (.symm
                        (.assoc w27 w43 w653)
                      )
                      (.mul
                        (.swap w27 w43)
                        (.refl w653)
                      )
                    )
                    (.mul
                      (.trans
                        (.mul
                        (.mul
                        (.refl w43)
                        (.refl w27)
                        )
                        (.deep w654)
                        )
                        (.mul_one w655)
                      )
                      (.refl w653)
                    )
                  )
                  (.assoc w43 w27 w653)
                )
              )
            )
          )
        )
      )
    )
  )
)

private theorem trace35_checked : trace35.check = true := by decide

private theorem trace35_sound :
    eval dmModel.val trace35.lhs = eval dmModel.val trace35.rhs :=
  Deriv.sound dmModel trace35 trace35_checked

private def trace36 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.trans
                (.trans
                  (.symm
                    (.assoc w29 w43 w656)
                  )
                  (.mul
                    (.mul_inv w29)
                    (.refl w656)
                  )
                )
                (.one_mul w656)
              )
            )
          )
        )
      )
    )
  )
)

private theorem trace36_checked : trace36.check = true := by decide

private theorem trace36_sound :
    eval dmModel.val trace36.lhs = eval dmModel.val trace36.rhs :=
  Deriv.sound dmModel trace36 trace36_checked

private def trace37 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w64)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.symm
                        (.inv_comm w54 w61)
                        )
                        (.refl w575)
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

private theorem trace37_checked : trace37.check = true := by decide

private theorem trace37_sound :
    eval dmModel.val trace37.lhs = eval dmModel.val trace37.rhs :=
  Deriv.sound dmModel trace37 trace37_checked

private def trace38 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w64)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w66 w657 w575)
                        )
                        (.mul
                        (.swap w66 w657)
                        (.refl w575)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w657)
                        (.refl w66)
                        )
                        (.deep w658)
                        )
                        (.mul_one w659)
                        )
                        (.refl w575)
                        )
                        )
                        (.assoc w657 w66 w575)
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

private theorem trace38_checked : trace38.check = true := by decide

private theorem trace38_sound :
    eval dmModel.val trace38.lhs = eval dmModel.val trace38.rhs :=
  Deriv.sound dmModel trace38 trace38_checked

private def trace39 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w64)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w68 w657 w660)
                        )
                        (.mul
                        (.swap w68 w657)
                        (.refl w660)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w657)
                        (.refl w68)
                        )
                        (.deep w661)
                        )
                        (.mul_one w662)
                        )
                        (.refl w660)
                        )
                        )
                        (.assoc w657 w68 w660)
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

private theorem trace39_checked : trace39.check = true := by decide

private theorem trace39_sound :
    eval dmModel.val trace39.lhs = eval dmModel.val trace39.rhs :=
  Deriv.sound dmModel trace39 trace39_checked

private def trace40 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w64)
                        (.mul
                        (.refl w62)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w61 w657 w663)
                        )
                        (.mul
                        (.swap w61 w657)
                        (.refl w663)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w657)
                        (.refl w61)
                        )
                        (.deep w664)
                        )
                        (.mul_one w665)
                        )
                        (.refl w663)
                        )
                        )
                        (.assoc w657 w61 w663)
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

private theorem trace40_checked : trace40.check = true := by decide

private theorem trace40_sound :
    eval dmModel.val trace40.lhs = eval dmModel.val trace40.rhs :=
  Deriv.sound dmModel trace40 trace40_checked

private def trace41 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w64)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w62 w657 w666)
                        )
                        (.mul
                        (.swap w62 w657)
                        (.refl w666)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w657)
                        (.refl w62)
                        )
                        (.deep w667)
                        )
                        (.mul_one w668)
                        )
                        (.refl w666)
                        )
                        )
                        (.assoc w657 w62 w666)
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

private theorem trace41_checked : trace41.check = true := by decide

private theorem trace41_sound :
    eval dmModel.val trace41.lhs = eval dmModel.val trace41.rhs :=
  Deriv.sound dmModel trace41 trace41_checked

private def trace42 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w64 w657 w669)
                        )
                        (.mul
                        (.mul_inv w64)
                        (.refl w669)
                        )
                        )
                        (.one_mul w669)
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

private theorem trace42_checked : trace42.check = true := by decide

private theorem trace42_sound :
    eval dmModel.val trace42.lhs = eval dmModel.val trace42.rhs :=
  Deriv.sound dmModel trace42 trace42_checked

private def trace43 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w73)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.symm
                        (.inv_comm w70 w61)
                        )
                        (.refl w572)
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

private theorem trace43_checked : trace43.check = true := by decide

private theorem trace43_sound :
    eval dmModel.val trace43.lhs = eval dmModel.val trace43.rhs :=
  Deriv.sound dmModel trace43 trace43_checked

private def trace44 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w73)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w71 w670 w572)
                        )
                        (.mul
                        (.swap w71 w670)
                        (.refl w572)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w670)
                        (.refl w71)
                        )
                        (.deep w671)
                        )
                        (.mul_one w672)
                        )
                        (.refl w572)
                        )
                        )
                        (.assoc w670 w71 w572)
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

private theorem trace44_checked : trace44.check = true := by decide

private theorem trace44_sound :
    eval dmModel.val trace44.lhs = eval dmModel.val trace44.rhs :=
  Deriv.sound dmModel trace44 trace44_checked

private def trace45 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w73 w670 w673)
                        )
                        (.mul
                        (.mul_inv w73)
                        (.refl w673)
                        )
                        )
                        (.one_mul w673)
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

private theorem trace45_checked : trace45.check = true := by decide

private theorem trace45_sound :
    eval dmModel.val trace45.lhs = eval dmModel.val trace45.rhs :=
  Deriv.sound dmModel trace45 trace45_checked

private def trace46 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.mul
                        (.refl w276)
                        (.mul
                        (.refl w272)
                        (.mul
                        (.refl w268)
                        (.mul
                        (.symm
                        (.inv_comm w152 w2)
                        )
                        (.refl w508)
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

private theorem trace46_checked : trace46.check = true := by decide

private theorem trace46_sound :
    eval dmModel.val trace46.lhs = eval dmModel.val trace46.rhs :=
  Deriv.sound dmModel trace46 trace46_checked

private def trace47 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.mul
                        (.refl w276)
                        (.mul
                        (.refl w272)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w268 w674 w508)
                        )
                        (.mul
                        (.swap w268 w674)
                        (.refl w508)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w268)
                        )
                        (.deep w675)
                        )
                        (.mul_one w676)
                        )
                        (.refl w508)
                        )
                        )
                        (.assoc w674 w268 w508)
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

private theorem trace47_checked : trace47.check = true := by decide

private theorem trace47_sound :
    eval dmModel.val trace47.lhs = eval dmModel.val trace47.rhs :=
  Deriv.sound dmModel trace47 trace47_checked

private def trace48 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.mul
                        (.refl w276)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w272 w674 w677)
                        )
                        (.mul
                        (.swap w272 w674)
                        (.refl w677)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w272)
                        )
                        (.deep w678)
                        )
                        (.mul_one w679)
                        )
                        (.refl w677)
                        )
                        )
                        (.assoc w674 w272 w677)
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

private theorem trace48_checked : trace48.check = true := by decide

private theorem trace48_sound :
    eval dmModel.val trace48.lhs = eval dmModel.val trace48.rhs :=
  Deriv.sound dmModel trace48 trace48_checked

private def trace49 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w276 w674 w680)
                        )
                        (.mul
                        (.swap w276 w674)
                        (.refl w680)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w276)
                        )
                        (.deep w681)
                        )
                        (.mul_one w682)
                        )
                        (.refl w680)
                        )
                        )
                        (.assoc w674 w276 w680)
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

private theorem trace49_checked : trace49.check = true := by decide

private theorem trace49_sound :
    eval dmModel.val trace49.lhs = eval dmModel.val trace49.rhs :=
  Deriv.sound dmModel trace49 trace49_checked

private def trace50 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w257 w674 w683)
                        )
                        (.mul
                        (.swap w257 w674)
                        (.refl w683)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w257)
                        )
                        (.deep w684)
                        )
                        (.mul_one w685)
                        )
                        (.refl w683)
                        )
                        )
                        (.assoc w674 w257 w683)
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

private theorem trace50_checked : trace50.check = true := by decide

private theorem trace50_sound :
    eval dmModel.val trace50.lhs = eval dmModel.val trace50.rhs :=
  Deriv.sound dmModel trace50 trace50_checked

private def trace51 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w252 w674 w686)
                        )
                        (.mul
                        (.swap w252 w674)
                        (.refl w686)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w252)
                        )
                        (.deep w687)
                        )
                        (.mul_one w688)
                        )
                        (.refl w686)
                        )
                        )
                        (.assoc w674 w252 w686)
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

private theorem trace51_checked : trace51.check = true := by decide

private theorem trace51_sound :
    eval dmModel.val trace51.lhs = eval dmModel.val trace51.rhs :=
  Deriv.sound dmModel trace51 trace51_checked

private def trace52 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w247 w674 w689)
                        )
                        (.mul
                        (.swap w247 w674)
                        (.refl w689)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w247)
                        )
                        (.deep w690)
                        )
                        (.mul_one w691)
                        )
                        (.refl w689)
                        )
                        )
                        (.assoc w674 w247 w689)
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

private theorem trace52_checked : trace52.check = true := by decide

private theorem trace52_sound :
    eval dmModel.val trace52.lhs = eval dmModel.val trace52.rhs :=
  Deriv.sound dmModel trace52 trace52_checked

private def trace53 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w241 w674 w692)
                        )
                        (.mul
                        (.swap w241 w674)
                        (.refl w692)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w241)
                        )
                        (.deep w693)
                        )
                        (.mul_one w694)
                        )
                        (.refl w692)
                        )
                        )
                        (.assoc w674 w241 w692)
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

private theorem trace53_checked : trace53.check = true := by decide

private theorem trace53_sound :
    eval dmModel.val trace53.lhs = eval dmModel.val trace53.rhs :=
  Deriv.sound dmModel trace53 trace53_checked

private def trace54 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w235 w674 w695)
                        )
                        (.mul
                        (.swap w235 w674)
                        (.refl w695)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w235)
                        )
                        (.deep w696)
                        )
                        (.mul_one w697)
                        )
                        (.refl w695)
                        )
                        )
                        (.assoc w674 w235 w695)
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

private theorem trace54_checked : trace54.check = true := by decide

private theorem trace54_sound :
    eval dmModel.val trace54.lhs = eval dmModel.val trace54.rhs :=
  Deriv.sound dmModel trace54 trace54_checked

private def trace55 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w229 w674 w698)
                        )
                        (.mul
                        (.swap w229 w674)
                        (.refl w698)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w229)
                        )
                        (.deep w699)
                        )
                        (.mul_one w700)
                        )
                        (.refl w698)
                        )
                        )
                        (.assoc w674 w229 w698)
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

private theorem trace55_checked : trace55.check = true := by decide

private theorem trace55_sound :
    eval dmModel.val trace55.lhs = eval dmModel.val trace55.rhs :=
  Deriv.sound dmModel trace55 trace55_checked

private def trace56 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w223 w674 w701)
                        )
                        (.mul
                        (.swap w223 w674)
                        (.refl w701)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w223)
                        )
                        (.deep w702)
                        )
                        (.mul_one w703)
                        )
                        (.refl w701)
                        )
                        )
                        (.assoc w674 w223 w701)
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

private theorem trace56_checked : trace56.check = true := by decide

private theorem trace56_sound :
    eval dmModel.val trace56.lhs = eval dmModel.val trace56.rhs :=
  Deriv.sound dmModel trace56 trace56_checked

private def trace57 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w217 w674 w704)
                        )
                        (.mul
                        (.swap w217 w674)
                        (.refl w704)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w217)
                        )
                        (.deep w705)
                        )
                        (.mul_one w706)
                        )
                        (.refl w704)
                        )
                        )
                        (.assoc w674 w217 w704)
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

private theorem trace57_checked : trace57.check = true := by decide

private theorem trace57_sound :
    eval dmModel.val trace57.lhs = eval dmModel.val trace57.rhs :=
  Deriv.sound dmModel trace57 trace57_checked

private def trace58 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w212 w674 w707)
                        )
                        (.mul
                        (.swap w212 w674)
                        (.refl w707)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w212)
                        )
                        (.deep w708)
                        )
                        (.mul_one w709)
                        )
                        (.refl w707)
                        )
                        )
                        (.assoc w674 w212 w707)
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

private theorem trace58_checked : trace58.check = true := by decide

private theorem trace58_sound :
    eval dmModel.val trace58.lhs = eval dmModel.val trace58.rhs :=
  Deriv.sound dmModel trace58 trace58_checked

private def trace59 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w416 w674 w710)
                        )
                        (.mul
                        (.swap w416 w674)
                        (.refl w710)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w416)
                        )
                        (.deep w711)
                        )
                        (.mul_one w712)
                        )
                        (.refl w710)
                        )
                        )
                        (.assoc w674 w416 w710)
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

private theorem trace59_checked : trace59.check = true := by decide

private theorem trace59_sound :
    eval dmModel.val trace59.lhs = eval dmModel.val trace59.rhs :=
  Deriv.sound dmModel trace59 trace59_checked

private def trace60 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w208 w674 w713)
                        )
                        (.mul
                        (.swap w208 w674)
                        (.refl w713)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w208)
                        )
                        (.deep w714)
                        )
                        (.mul_one w715)
                        )
                        (.refl w713)
                        )
                        )
                        (.assoc w674 w208 w713)
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

private theorem trace60_checked : trace60.check = true := by decide

private theorem trace60_sound :
    eval dmModel.val trace60.lhs = eval dmModel.val trace60.rhs :=
  Deriv.sound dmModel trace60 trace60_checked

private def trace61 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w204 w674 w716)
                        )
                        (.mul
                        (.swap w204 w674)
                        (.refl w716)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w204)
                        )
                        (.deep w717)
                        )
                        (.mul_one w718)
                        )
                        (.refl w716)
                        )
                        )
                        (.assoc w674 w204 w716)
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

private theorem trace61_checked : trace61.check = true := by decide

private theorem trace61_sound :
    eval dmModel.val trace61.lhs = eval dmModel.val trace61.rhs :=
  Deriv.sound dmModel trace61 trace61_checked

private def trace62 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w196)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w200 w674 w719)
                        )
                        (.mul
                        (.swap w200 w674)
                        (.refl w719)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w674)
                        (.refl w200)
                        )
                        (.deep w720)
                        )
                        (.mul_one w721)
                        )
                        (.refl w719)
                        )
                        )
                        (.assoc w674 w200 w719)
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

private theorem trace62_checked : trace62.check = true := by decide

private theorem trace62_sound :
    eval dmModel.val trace62.lhs = eval dmModel.val trace62.rhs :=
  Deriv.sound dmModel trace62 trace62_checked

private def trace63 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w196 w674 w722)
                        )
                        (.mul
                        (.mul_inv w196)
                        (.refl w722)
                        )
                        )
                        (.one_mul w722)
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

private theorem trace63_checked : trace63.check = true := by decide

private theorem trace63_sound :
    eval dmModel.val trace63.lhs = eval dmModel.val trace63.rhs :=
  Deriv.sound dmModel trace63 trace63_checked

private def trace64 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.mul
                        (.refl w276)
                        (.mul
                        (.symm
                        (.inv_comm w157 w2)
                        )
                        (.refl w677)
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

private theorem trace64_checked : trace64.check = true := by decide

private theorem trace64_sound :
    eval dmModel.val trace64.lhs = eval dmModel.val trace64.rhs :=
  Deriv.sound dmModel trace64 trace64_checked

private def trace65 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w276 w723 w677)
                        )
                        (.mul
                        (.swap w276 w723)
                        (.refl w677)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w276)
                        )
                        (.deep w724)
                        )
                        (.mul_one w725)
                        )
                        (.refl w677)
                        )
                        )
                        (.assoc w723 w276 w677)
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

private theorem trace65_checked : trace65.check = true := by decide

private theorem trace65_sound :
    eval dmModel.val trace65.lhs = eval dmModel.val trace65.rhs :=
  Deriv.sound dmModel trace65 trace65_checked

private def trace66 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w257 w723 w726)
                        )
                        (.mul
                        (.swap w257 w723)
                        (.refl w726)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w257)
                        )
                        (.deep w727)
                        )
                        (.mul_one w728)
                        )
                        (.refl w726)
                        )
                        )
                        (.assoc w723 w257 w726)
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

private theorem trace66_checked : trace66.check = true := by decide

private theorem trace66_sound :
    eval dmModel.val trace66.lhs = eval dmModel.val trace66.rhs :=
  Deriv.sound dmModel trace66 trace66_checked

private def trace67 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w252 w723 w729)
                        )
                        (.mul
                        (.swap w252 w723)
                        (.refl w729)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w252)
                        )
                        (.deep w730)
                        )
                        (.mul_one w731)
                        )
                        (.refl w729)
                        )
                        )
                        (.assoc w723 w252 w729)
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

private theorem trace67_checked : trace67.check = true := by decide

private theorem trace67_sound :
    eval dmModel.val trace67.lhs = eval dmModel.val trace67.rhs :=
  Deriv.sound dmModel trace67 trace67_checked

private def trace68 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w247 w723 w732)
                        )
                        (.mul
                        (.swap w247 w723)
                        (.refl w732)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w247)
                        )
                        (.deep w733)
                        )
                        (.mul_one w734)
                        )
                        (.refl w732)
                        )
                        )
                        (.assoc w723 w247 w732)
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

private theorem trace68_checked : trace68.check = true := by decide

private theorem trace68_sound :
    eval dmModel.val trace68.lhs = eval dmModel.val trace68.rhs :=
  Deriv.sound dmModel trace68 trace68_checked

private def trace69 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w241 w723 w735)
                        )
                        (.mul
                        (.swap w241 w723)
                        (.refl w735)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w241)
                        )
                        (.deep w736)
                        )
                        (.mul_one w737)
                        )
                        (.refl w735)
                        )
                        )
                        (.assoc w723 w241 w735)
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

private theorem trace69_checked : trace69.check = true := by decide

private theorem trace69_sound :
    eval dmModel.val trace69.lhs = eval dmModel.val trace69.rhs :=
  Deriv.sound dmModel trace69 trace69_checked

private def trace70 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w235 w723 w738)
                        )
                        (.mul
                        (.swap w235 w723)
                        (.refl w738)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w235)
                        )
                        (.deep w739)
                        )
                        (.mul_one w740)
                        )
                        (.refl w738)
                        )
                        )
                        (.assoc w723 w235 w738)
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

private theorem trace70_checked : trace70.check = true := by decide

private theorem trace70_sound :
    eval dmModel.val trace70.lhs = eval dmModel.val trace70.rhs :=
  Deriv.sound dmModel trace70 trace70_checked

private def trace71 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w229 w723 w741)
                        )
                        (.mul
                        (.swap w229 w723)
                        (.refl w741)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w229)
                        )
                        (.deep w742)
                        )
                        (.mul_one w743)
                        )
                        (.refl w741)
                        )
                        )
                        (.assoc w723 w229 w741)
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

private theorem trace71_checked : trace71.check = true := by decide

private theorem trace71_sound :
    eval dmModel.val trace71.lhs = eval dmModel.val trace71.rhs :=
  Deriv.sound dmModel trace71 trace71_checked

private def trace72 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w223 w723 w744)
                        )
                        (.mul
                        (.swap w223 w723)
                        (.refl w744)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w223)
                        )
                        (.deep w745)
                        )
                        (.mul_one w746)
                        )
                        (.refl w744)
                        )
                        )
                        (.assoc w723 w223 w744)
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

private theorem trace72_checked : trace72.check = true := by decide

private theorem trace72_sound :
    eval dmModel.val trace72.lhs = eval dmModel.val trace72.rhs :=
  Deriv.sound dmModel trace72 trace72_checked

private def trace73 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w217 w723 w747)
                        )
                        (.mul
                        (.swap w217 w723)
                        (.refl w747)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w217)
                        )
                        (.deep w748)
                        )
                        (.mul_one w749)
                        )
                        (.refl w747)
                        )
                        )
                        (.assoc w723 w217 w747)
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

private theorem trace73_checked : trace73.check = true := by decide

private theorem trace73_sound :
    eval dmModel.val trace73.lhs = eval dmModel.val trace73.rhs :=
  Deriv.sound dmModel trace73 trace73_checked

private def trace74 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w212 w723 w750)
                        )
                        (.mul
                        (.swap w212 w723)
                        (.refl w750)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w212)
                        )
                        (.deep w751)
                        )
                        (.mul_one w752)
                        )
                        (.refl w750)
                        )
                        )
                        (.assoc w723 w212 w750)
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

private theorem trace74_checked : trace74.check = true := by decide

private theorem trace74_sound :
    eval dmModel.val trace74.lhs = eval dmModel.val trace74.rhs :=
  Deriv.sound dmModel trace74 trace74_checked

private def trace75 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.mul
                        (.refl w208)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w416 w723 w753)
                        )
                        (.mul
                        (.swap w416 w723)
                        (.refl w753)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w416)
                        )
                        (.deep w754)
                        )
                        (.mul_one w755)
                        )
                        (.refl w753)
                        )
                        )
                        (.assoc w723 w416 w753)
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

private theorem trace75_checked : trace75.check = true := by decide

private theorem trace75_sound :
    eval dmModel.val trace75.lhs = eval dmModel.val trace75.rhs :=
  Deriv.sound dmModel trace75 trace75_checked

private def trace76 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w204)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w208 w723 w756)
                        )
                        (.mul
                        (.swap w208 w723)
                        (.refl w756)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w723)
                        (.refl w208)
                        )
                        (.deep w757)
                        )
                        (.mul_one w758)
                        )
                        (.refl w756)
                        )
                        )
                        (.assoc w723 w208 w756)
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

private theorem trace76_checked : trace76.check = true := by decide

private theorem trace76_sound :
    eval dmModel.val trace76.lhs = eval dmModel.val trace76.rhs :=
  Deriv.sound dmModel trace76 trace76_checked

private def trace77 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w204 w723 w759)
                        )
                        (.mul
                        (.mul_inv w204)
                        (.refl w759)
                        )
                        )
                        (.one_mul w759)
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

private theorem trace77_checked : trace77.check = true := by decide

private theorem trace77_sound :
    eval dmModel.val trace77.lhs = eval dmModel.val trace77.rhs :=
  Deriv.sound dmModel trace77 trace77_checked

private def trace78 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.mul
                        (.refl w257)
                        (.mul
                        (.symm
                        (.inv_comm w162 w2)
                        )
                        (.refl w677)
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

private theorem trace78_checked : trace78.check = true := by decide

private theorem trace78_sound :
    eval dmModel.val trace78.lhs = eval dmModel.val trace78.rhs :=
  Deriv.sound dmModel trace78 trace78_checked

private def trace79 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.mul
                        (.refl w252)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w257 w760 w677)
                        )
                        (.mul
                        (.swap w257 w760)
                        (.refl w677)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w257)
                        )
                        (.deep w761)
                        )
                        (.mul_one w762)
                        )
                        (.refl w677)
                        )
                        )
                        (.assoc w760 w257 w677)
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

private theorem trace79_checked : trace79.check = true := by decide

private theorem trace79_sound :
    eval dmModel.val trace79.lhs = eval dmModel.val trace79.rhs :=
  Deriv.sound dmModel trace79 trace79_checked

private def trace80 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.mul
                        (.refl w247)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w252 w760 w763)
                        )
                        (.mul
                        (.swap w252 w760)
                        (.refl w763)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w252)
                        )
                        (.deep w764)
                        )
                        (.mul_one w765)
                        )
                        (.refl w763)
                        )
                        )
                        (.assoc w760 w252 w763)
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

private theorem trace80_checked : trace80.check = true := by decide

private theorem trace80_sound :
    eval dmModel.val trace80.lhs = eval dmModel.val trace80.rhs :=
  Deriv.sound dmModel trace80 trace80_checked

private def trace81 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.mul
                        (.refl w241)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w247 w760 w766)
                        )
                        (.mul
                        (.swap w247 w760)
                        (.refl w766)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w247)
                        )
                        (.deep w767)
                        )
                        (.mul_one w768)
                        )
                        (.refl w766)
                        )
                        )
                        (.assoc w760 w247 w766)
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

private theorem trace81_checked : trace81.check = true := by decide

private theorem trace81_sound :
    eval dmModel.val trace81.lhs = eval dmModel.val trace81.rhs :=
  Deriv.sound dmModel trace81 trace81_checked

private def trace82 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.mul
                        (.refl w235)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w241 w760 w769)
                        )
                        (.mul
                        (.swap w241 w760)
                        (.refl w769)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w241)
                        )
                        (.deep w770)
                        )
                        (.mul_one w771)
                        )
                        (.refl w769)
                        )
                        )
                        (.assoc w760 w241 w769)
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

private theorem trace82_checked : trace82.check = true := by decide

private theorem trace82_sound :
    eval dmModel.val trace82.lhs = eval dmModel.val trace82.rhs :=
  Deriv.sound dmModel trace82 trace82_checked

private def trace83 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.mul
                        (.refl w229)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w235 w760 w772)
                        )
                        (.mul
                        (.swap w235 w760)
                        (.refl w772)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w235)
                        )
                        (.deep w773)
                        )
                        (.mul_one w774)
                        )
                        (.refl w772)
                        )
                        )
                        (.assoc w760 w235 w772)
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

private theorem trace83_checked : trace83.check = true := by decide

private theorem trace83_sound :
    eval dmModel.val trace83.lhs = eval dmModel.val trace83.rhs :=
  Deriv.sound dmModel trace83 trace83_checked

private def trace84 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.mul
                        (.refl w223)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w229 w760 w775)
                        )
                        (.mul
                        (.swap w229 w760)
                        (.refl w775)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w229)
                        )
                        (.deep w776)
                        )
                        (.mul_one w777)
                        )
                        (.refl w775)
                        )
                        )
                        (.assoc w760 w229 w775)
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

private theorem trace84_checked : trace84.check = true := by decide

private theorem trace84_sound :
    eval dmModel.val trace84.lhs = eval dmModel.val trace84.rhs :=
  Deriv.sound dmModel trace84 trace84_checked

private def trace85 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.mul
                        (.refl w217)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w223 w760 w778)
                        )
                        (.mul
                        (.swap w223 w760)
                        (.refl w778)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w223)
                        )
                        (.deep w779)
                        )
                        (.mul_one w780)
                        )
                        (.refl w778)
                        )
                        )
                        (.assoc w760 w223 w778)
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

private theorem trace85_checked : trace85.check = true := by decide

private theorem trace85_sound :
    eval dmModel.val trace85.lhs = eval dmModel.val trace85.rhs :=
  Deriv.sound dmModel trace85 trace85_checked

private def trace86 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.mul
                        (.refl w212)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w217 w760 w781)
                        )
                        (.mul
                        (.swap w217 w760)
                        (.refl w781)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w217)
                        )
                        (.deep w782)
                        )
                        (.mul_one w783)
                        )
                        (.refl w781)
                        )
                        )
                        (.assoc w760 w217 w781)
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

private theorem trace86_checked : trace86.check = true := by decide

private theorem trace86_sound :
    eval dmModel.val trace86.lhs = eval dmModel.val trace86.rhs :=
  Deriv.sound dmModel trace86 trace86_checked

private def trace87 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.mul
                        (.refl w416)
                        (.trans
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w212 w760 w784)
                        )
                        (.mul
                        (.swap w212 w760)
                        (.refl w784)
                        )
                        )
                        (.mul
                        (.trans
                        (.mul
                        (.mul
                        (.refl w760)
                        (.refl w212)
                        )
                        (.deep w785)
                        )
                        (.mul_one w786)
                        )
                        (.refl w784)
                        )
                        )
                        (.assoc w760 w212 w784)
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

private theorem trace87_checked : trace87.check = true := by decide

private theorem trace87_sound :
    eval dmModel.val trace87.lhs = eval dmModel.val trace87.rhs :=
  Deriv.sound dmModel trace87 trace87_checked

private def trace88 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.mul
      (.refl w88)
      (.mul
        (.refl w9)
        (.mul
          (.refl w46)
          (.mul
            (.refl w25)
            (.mul
              (.refl w27)
              (.mul
                (.refl w27)
                (.mul
                  (.refl w11)
                  (.mul
                    (.refl w42)
                    (.mul
                      (.refl w48)
                      (.mul
                        (.refl w53)
                        (.mul
                        (.refl w324)
                        (.mul
                        (.refl w58)
                        (.mul
                        (.refl w59)
                        (.mul
                        (.refl w326)
                        (.mul
                        (.refl w62)
                        (.mul
                        (.refl w61)
                        (.mul
                        (.refl w68)
                        (.mul
                        (.refl w66)
                        (.mul
                        (.refl w71)
                        (.mul
                        (.refl w98)
                        (.mul
                        (.refl w94)
                        (.mul
                        (.refl w107)
                        (.mul
                        (.refl w103)
                        (.mul
                        (.refl w130)
                        (.mul
                        (.refl w135)
                        (.mul
                        (.refl w164)
                        (.mul
                        (.refl w165)
                        (.mul
                        (.refl w169)
                        (.mul
                        (.refl w173)
                        (.mul
                        (.refl w177)
                        (.mul
                        (.refl w181)
                        (.mul
                        (.refl w185)
                        (.mul
                        (.refl w188)
                        (.mul
                        (.refl w192)
                        (.mul
                        (.refl w200)
                        (.mul
                        (.refl w208)
                        (.trans
                        (.trans
                        (.symm
                        (.assoc w416 w760 w787)
                        )
                        (.mul
                        (.mul_inv w416)
                        (.refl w787)
                        )
                        )
                        (.one_mul w787)
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

private theorem trace88_checked : trace88.check = true := by decide

private theorem trace88_sound :
    eval dmModel.val trace88.lhs = eval dmModel.val trace88.rhs :=
  Deriv.sound dmModel trace88 trace88_checked

private def trace89 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w9)
    (.trans
      (.trans
        (.trans
          (.symm
            (.assoc w88 w9 w821)
          )
          (.mul
            (.swap w88 w9)
            (.refl w821)
          )
        )
        (.mul
          (.trans
            (.mul
              (.mul
                (.refl w9)
                (.refl w88)
              )
              (.deep w822)
            )
            (.mul_one w823)
          )
          (.refl w821)
        )
      )
      (.assoc w9 w88 w821)
    )
  )
)

private theorem trace89_checked : trace89.check = true := by decide

private theorem trace89_sound :
    eval dmModel.val trace89.lhs = eval dmModel.val trace89.rhs :=
  Deriv.sound dmModel trace89 trace89_checked

private def trace90 : Deriv :=
  (.mul
  (.refl w82)
  (.trans
    (.symm
      (.assoc w9 w9 w824)
    )
    (.mul
      (.mul_self w9)
      (.refl w824)
    )
  )
)

private theorem trace90_checked : trace90.check = true := by decide

private theorem trace90_sound :
    eval dmModel.val trace90.lhs = eval dmModel.val trace90.rhs :=
  Deriv.sound dmModel trace90 trace90_checked

private def trace91 : Deriv :=
  (.mul
  (.refl w82)
  (.mul
    (.refl w825)
    (.mul
      (.refl w88)
      (.mul
        (.refl w46)
        (.mul
          (.refl w25)
          (.trans
            (.symm
              (.assoc w27 w27 w817)
            )
            (.mul
              (.mul_self w27)
              (.refl w817)
            )
          )
        )
      )
    )
  )
)

private theorem trace91_checked : trace91.check = true := by decide

private theorem trace91_sound :
    eval dmModel.val trace91.lhs = eval dmModel.val trace91.rhs :=
  Deriv.sound dmModel trace91 trace91_checked

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
    eval dmModel.val trace24.lhs = eval dmModel.val trace31.rhs :=
  calc
    _ = eval dmModel.val trace24.rhs := trace24_sound
    _ = eval dmModel.val trace25.rhs := trace25_sound
    _ = eval dmModel.val trace26.rhs := trace26_sound
    _ = eval dmModel.val trace27.rhs := trace27_sound
    _ = eval dmModel.val trace28.rhs := trace28_sound
    _ = eval dmModel.val trace29.rhs := trace29_sound
    _ = eval dmModel.val trace30.rhs := trace30_sound
    _ = eval dmModel.val trace31.rhs := trace31_sound

private theorem block4_sound :
    eval dmModel.val trace32.lhs = eval dmModel.val trace39.rhs :=
  calc
    _ = eval dmModel.val trace32.rhs := trace32_sound
    _ = eval dmModel.val trace33.rhs := trace33_sound
    _ = eval dmModel.val trace34.rhs := trace34_sound
    _ = eval dmModel.val trace35.rhs := trace35_sound
    _ = eval dmModel.val trace36.rhs := trace36_sound
    _ = eval dmModel.val trace37.rhs := trace37_sound
    _ = eval dmModel.val trace38.rhs := trace38_sound
    _ = eval dmModel.val trace39.rhs := trace39_sound

private theorem block5_sound :
    eval dmModel.val trace40.lhs = eval dmModel.val trace47.rhs :=
  calc
    _ = eval dmModel.val trace40.rhs := trace40_sound
    _ = eval dmModel.val trace41.rhs := trace41_sound
    _ = eval dmModel.val trace42.rhs := trace42_sound
    _ = eval dmModel.val trace43.rhs := trace43_sound
    _ = eval dmModel.val trace44.rhs := trace44_sound
    _ = eval dmModel.val trace45.rhs := trace45_sound
    _ = eval dmModel.val trace46.rhs := trace46_sound
    _ = eval dmModel.val trace47.rhs := trace47_sound

private theorem block6_sound :
    eval dmModel.val trace48.lhs = eval dmModel.val trace55.rhs :=
  calc
    _ = eval dmModel.val trace48.rhs := trace48_sound
    _ = eval dmModel.val trace49.rhs := trace49_sound
    _ = eval dmModel.val trace50.rhs := trace50_sound
    _ = eval dmModel.val trace51.rhs := trace51_sound
    _ = eval dmModel.val trace52.rhs := trace52_sound
    _ = eval dmModel.val trace53.rhs := trace53_sound
    _ = eval dmModel.val trace54.rhs := trace54_sound
    _ = eval dmModel.val trace55.rhs := trace55_sound

private theorem block7_sound :
    eval dmModel.val trace56.lhs = eval dmModel.val trace63.rhs :=
  calc
    _ = eval dmModel.val trace56.rhs := trace56_sound
    _ = eval dmModel.val trace57.rhs := trace57_sound
    _ = eval dmModel.val trace58.rhs := trace58_sound
    _ = eval dmModel.val trace59.rhs := trace59_sound
    _ = eval dmModel.val trace60.rhs := trace60_sound
    _ = eval dmModel.val trace61.rhs := trace61_sound
    _ = eval dmModel.val trace62.rhs := trace62_sound
    _ = eval dmModel.val trace63.rhs := trace63_sound

private theorem block8_sound :
    eval dmModel.val trace64.lhs = eval dmModel.val trace71.rhs :=
  calc
    _ = eval dmModel.val trace64.rhs := trace64_sound
    _ = eval dmModel.val trace65.rhs := trace65_sound
    _ = eval dmModel.val trace66.rhs := trace66_sound
    _ = eval dmModel.val trace67.rhs := trace67_sound
    _ = eval dmModel.val trace68.rhs := trace68_sound
    _ = eval dmModel.val trace69.rhs := trace69_sound
    _ = eval dmModel.val trace70.rhs := trace70_sound
    _ = eval dmModel.val trace71.rhs := trace71_sound

private theorem block9_sound :
    eval dmModel.val trace72.lhs = eval dmModel.val trace79.rhs :=
  calc
    _ = eval dmModel.val trace72.rhs := trace72_sound
    _ = eval dmModel.val trace73.rhs := trace73_sound
    _ = eval dmModel.val trace74.rhs := trace74_sound
    _ = eval dmModel.val trace75.rhs := trace75_sound
    _ = eval dmModel.val trace76.rhs := trace76_sound
    _ = eval dmModel.val trace77.rhs := trace77_sound
    _ = eval dmModel.val trace78.rhs := trace78_sound
    _ = eval dmModel.val trace79.rhs := trace79_sound

private theorem block10_sound :
    eval dmModel.val trace80.lhs = eval dmModel.val trace87.rhs :=
  calc
    _ = eval dmModel.val trace80.rhs := trace80_sound
    _ = eval dmModel.val trace81.rhs := trace81_sound
    _ = eval dmModel.val trace82.rhs := trace82_sound
    _ = eval dmModel.val trace83.rhs := trace83_sound
    _ = eval dmModel.val trace84.rhs := trace84_sound
    _ = eval dmModel.val trace85.rhs := trace85_sound
    _ = eval dmModel.val trace86.rhs := trace86_sound
    _ = eval dmModel.val trace87.rhs := trace87_sound

private theorem block11_sound :
    eval dmModel.val trace88.lhs = eval dmModel.val trace91.rhs :=
  calc
    _ = eval dmModel.val trace88.rhs := trace88_sound
    _ = eval dmModel.val trace89.rhs := trace89_sound
    _ = eval dmModel.val trace90.rhs := trace90_sound
    _ = eval dmModel.val trace91.rhs := trace91_sound

def checkedPrefix : List Deriv :=
  [ trace0, trace1, trace2, trace3, trace4,
    trace5, trace6, trace7, trace8, trace9,
    trace10, trace11, trace12, trace13, trace14,
    trace15, trace16, trace17, trace18, trace19,
    trace20, trace21, trace22, trace23, trace24,
    trace25, trace26, trace27, trace28, trace29,
    trace30, trace31, trace32, trace33, trace34,
    trace35, trace36, trace37, trace38, trace39,
    trace40, trace41, trace42, trace43, trace44,
    trace45, trace46, trace47, trace48, trace49,
    trace50, trace51, trace52, trace53, trace54,
    trace55, trace56, trace57, trace58, trace59,
    trace60, trace61, trace62, trace63, trace64,
    trace65, trace66, trace67, trace68, trace69,
    trace70, trace71, trace72, trace73, trace74,
    trace75, trace76, trace77, trace78, trace79,
    trace80, trace81, trace82, trace83, trace84,
    trace85, trace86, trace87, trace88, trace89,
    trace90, trace91 ]

theorem checkedPrefix_all_checked : checkedPrefix.all Deriv.check = true := by decide

def rightProduct : List CWord → CWord
  | [] => .one
  | [x] => x
  | x :: y :: xs => .mul x (rightProduct (y :: xs))

def endpointFactors : List CWord :=
  [ w82, w825, w88, w46, w25,
    w826, w11, w42, w48, w53,
    w324, w58, w59, w326, w62,
    w61, w68, w66, w71, w98,
    w94, w107, w103, w130, w135,
    w164, w165, w169, w173, w177,
    w181, w185, w188, w192, w200,
    w208, w212, w217, w223, w229,
    w235, w241, w247, w252, w257,
    w268, w262, w295, w291, w287,
    w285 ]

def endpoint : CWord := trace91.rhs

theorem endpointFactors_length : endpointFactors.length = 51 := by decide

theorem endpoint_eq_rightProduct : endpoint = rightProduct endpointFactors := by decide

theorem endpoint_depthThreeFactors :
    endpointFactors.filter (fun w => decide (w.depth = 3)) =
      [ .sq (.comm (.gen .D) (.gen .B)),
        .comm (.comm (.gen .D) (.gen .B)) (.gen .B),
        .comm (.sq (.gen .B)) (.gen .D) ] := by decide

theorem trace0_lhs : trace0.lhs = certificateWord := by decide

private theorem generatedPrefix_sound :
    eval dmModel.val trace0.lhs = eval dmModel.val trace91.rhs :=
  calc
    _ = eval dmModel.val trace7.rhs := block0_sound
    _ = eval dmModel.val trace15.rhs := block1_sound
    _ = eval dmModel.val trace23.rhs := block2_sound
    _ = eval dmModel.val trace31.rhs := block3_sound
    _ = eval dmModel.val trace39.rhs := block4_sound
    _ = eval dmModel.val trace47.rhs := block5_sound
    _ = eval dmModel.val trace55.rhs := block6_sound
    _ = eval dmModel.val trace63.rhs := block7_sound
    _ = eval dmModel.val trace71.rhs := block8_sound
    _ = eval dmModel.val trace79.rhs := block9_sound
    _ = eval dmModel.val trace87.rhs := block10_sound
    _ = eval dmModel.val trace91.rhs := block11_sound

theorem eval_certificateWord_eq_endpoint :
    eval dmModel.val certificateWord = eval dmModel.val endpoint := by
  rw [← trace0_lhs]
  exact generatedPrefix_sound

#print axioms checkedPrefix_all_checked
#print axioms endpoint_depthThreeFactors
#print axioms generatedPrefix_sound
#print axioms eval_certificateWord_eq_endpoint

end GQ2.Dyadic.Instances.MpcC6WeightedTracePrefix
