import Fast.Five.Checks.Base
import Fast.Five.Checks.Cover
import Fast.Five.Checks.Psd00
import Fast.Five.Checks.Psd01
import Fast.Five.Checks.Expanded00
import Fast.Five.Checks.Expanded01
import Fast.Five.Checks.Expanded02
import Fast.Five.Checks.Expanded03
import Fast.Five.Checks.Psd10
import Fast.Five.Checks.Psd11
import Fast.Five.Checks.Expanded10
import Fast.Five.Checks.Expanded11
import Fast.Five.Checks.Expanded12
import Fast.Five.Checks.Expanded13
import Fast.Five.Checks.Psd20
import Fast.Five.Checks.Psd21
import Fast.Five.Checks.Expanded20
import Fast.Five.Checks.Expanded21
import Fast.Five.Checks.Expanded22
import Fast.Five.Checks.Expanded23
import Fast.Five.Checks.Psd30
import Fast.Five.Checks.Psd31
import Fast.Five.Checks.Psd32
import Fast.Five.Checks.Psd33
import Fast.Five.Checks.Psd34
import Fast.Five.Checks.Expanded30
import Fast.Five.Checks.Expanded31
import Fast.Five.Checks.Expanded32
import Fast.Five.Checks.Expanded33
import Fast.Five.Checks.Expanded34
import Fast.Five.Checks.Expanded35
import Fast.Five.Checks.Expanded36
import Fast.Five.Checks.Psd40
import Fast.Five.Checks.Psd41
import Fast.Five.Checks.Psd42
import Fast.Five.Checks.Psd43
import Fast.Five.Checks.Psd44
import Fast.Five.Checks.Expanded40
import Fast.Five.Checks.Expanded41
import Fast.Five.Checks.Expanded42
import Fast.Five.Checks.Expanded43
import Fast.Five.Checks.Expanded44
import Fast.Five.Checks.Psd50
import Fast.Five.Checks.Psd51
import Fast.Five.Checks.Psd52
import Fast.Five.Checks.Psd53
import Fast.Five.Checks.Expanded50
import Fast.Five.Checks.Expanded51
import Fast.Five.Checks.Expanded52
import Fast.Five.Checks.Expanded53
import Fast.Five.Checks.Expanded54
import Fast.Five.Checks.Endpoints0
import Fast.Five.Checks.Endpoints1
import Fast.Five.Checks.Endpoints2
import Fast.Five.Checks.Endpoints3
import Fast.Five.Checks.Endpoints4
import Fast.Five.Checks.Endpoints5
import Fast.Five.Checks.Endpoints6
import Fast.Five.Checks.Endpoints7
import Fast.Five.Checks.Endpoints8
import Fast.Five.Checks.Endpoints9
import Fast.Five.Checks.Endpoints10
import Fast.Five.Checks.Endpoints11
import Fast.Five.Checks.Endpoints12
import Fast.Five.Checks.Endpoints13
import Fast.Five.Checks.Endpoints14
import Fast.Five.Checks.Endpoints15
import Fast.Five.Checks.Endpoints16
import Fast.Five.Checks.Endpoints17
import Fast.Five.Checks.Endpoints18
import Fast.Five.Checks.Endpoints19
import Fast.Five.Checks.Endpoints20
import Fast.Five.Checks.Endpoints21
import Fast.Five.Checks.Endpoints22
import Fast.Five.Checks.Endpoints23
import Fast.Five.Checks.Endpoints24
import Fast.Five.Checks.Endpoints25
import Fast.Five.Checks.Endpoints26
import Fast.Five.Checks.Endpoints27
import Fast.Five.Checks.Endpoints28
import Fast.Five.Checks.Endpoints29
import Fast.Five.Checks.Endpoints30
import Fast.Five.Checks.Endpoints31
import Fast.Five.Checks.Endpoints32
import Fast.Five.Checks.Endpoints33
import Fast.Five.Checks.Endpoints34
import Fast.Five.Checks.Endpoints35
import Fast.Five.Checks.Endpoints36
import Fast.Five.Checks.Endpoints37
import Fast.Five.Checks.Endpoints38
import Fast.Five.Checks.Endpoints39
import Fast.Five.Checks.Endpoints40
import Fast.Five.Checks.Endpoints41
import Fast.Five.Checks.Endpoints42
import Fast.Five.Checks.Endpoints43
import Fast.Five.Checks.Endpoints44
import Fast.Five.Checks.Endpoints45
import Fast.Five.Checks.Endpoints46
import Fast.Five.Checks.Endpoints47
import Fast.Five.Checks.Endpoints48
import Fast.Five.Checks.Endpoints49
import Fast.Five.Checks.Endpoints50
import Fast.Five.Checks.Endpoints51
import Fast.Five.Checks.Endpoints52
import Fast.Five.Checks.Endpoints53
import Fast.Five.Checks.Endpoints54
import Fast.Five.Checks.Endpoints55
import Fast.Five.Checks.Endpoints56
import Fast.Five.Checks.Endpoints57
import Fast.Five.Checks.Endpoints58
import Fast.Five.Checks.Endpoints59
import Fast.Five.Checks.Endpoints60
import Fast.Five.Checks.Endpoints61
import Fast.Five.Checks.Endpoints62
import Fast.Five.Checks.Endpoints63
import Fast.Five.Checks.Endpoints64
import Fast.Five.Checks.Endpoints65
import Fast.Five.Checks.Endpoints66
import Fast.Five.Checks.Endpoints67
import Fast.Five.Checks.Endpoints68
import Fast.Five.Checks.Endpoints69
import Fast.Five.Checks.Endpoints70
import Fast.Five.Checks.Endpoints71
import Fast.Five.Checks.Endpoints72
import Fast.Five.Checks.Endpoints73
import Fast.Five.Checks.Endpoints74
import Fast.Five.Checks.Endpoints75
import Fast.Five.Checks.Endpoints76

set_option maxRecDepth 10000

set_option maxHeartbeats 0

namespace Fast.Five.Checked

theorem psd0 : (List.range 7).all (psdRow Data.low Data.high Data.block0) = true := by
  change (psdRow Data.low Data.high Data.block0 0 && (psdRow Data.low Data.high Data.block0 1 && (psdRow Data.low Data.high Data.block0 2 && (psdRow Data.low Data.high Data.block0 3 && (psdRow Data.low Data.high Data.block0 4 && (psdRow Data.low Data.high Data.block0 5 && (psdRow Data.low Data.high Data.block0 6 && true))))))) = true
  simp only [psd0_0, psd0_1, psd0_2, psd0_3, psd0_4, psd0_5, psd0_6, Bool.true_and]

theorem expanded0 : (List.range 15).all (expandedRow Data.block0) = true := by
  change (expandedRow Data.block0 0 && (expandedRow Data.block0 1 && (expandedRow Data.block0 2 && (expandedRow Data.block0 3 && (expandedRow Data.block0 4 && (expandedRow Data.block0 5 && (expandedRow Data.block0 6 && (expandedRow Data.block0 7 && (expandedRow Data.block0 8 && (expandedRow Data.block0 9 && (expandedRow Data.block0 10 && (expandedRow Data.block0 11 && (expandedRow Data.block0 12 && (expandedRow Data.block0 13 && (expandedRow Data.block0 14 && true))))))))))))))) = true
  simp only [expanded0_0, expanded0_1, expanded0_2, expanded0_3, expanded0_4, expanded0_5, expanded0_6, expanded0_7, expanded0_8, expanded0_9, expanded0_10, expanded0_11, expanded0_12, expanded0_13, expanded0_14, Bool.true_and]

theorem psd1 : (List.range 5).all (psdRow Data.low Data.high Data.block1) = true := by
  change (psdRow Data.low Data.high Data.block1 0 && (psdRow Data.low Data.high Data.block1 1 && (psdRow Data.low Data.high Data.block1 2 && (psdRow Data.low Data.high Data.block1 3 && (psdRow Data.low Data.high Data.block1 4 && true))))) = true
  simp only [psd1_0, psd1_1, psd1_2, psd1_3, psd1_4, Bool.true_and]

theorem expanded1 : (List.range 15).all (expandedRow Data.block1) = true := by
  change (expandedRow Data.block1 0 && (expandedRow Data.block1 1 && (expandedRow Data.block1 2 && (expandedRow Data.block1 3 && (expandedRow Data.block1 4 && (expandedRow Data.block1 5 && (expandedRow Data.block1 6 && (expandedRow Data.block1 7 && (expandedRow Data.block1 8 && (expandedRow Data.block1 9 && (expandedRow Data.block1 10 && (expandedRow Data.block1 11 && (expandedRow Data.block1 12 && (expandedRow Data.block1 13 && (expandedRow Data.block1 14 && true))))))))))))))) = true
  simp only [expanded1_0, expanded1_1, expanded1_2, expanded1_3, expanded1_4, expanded1_5, expanded1_6, expanded1_7, expanded1_8, expanded1_9, expanded1_10, expanded1_11, expanded1_12, expanded1_13, expanded1_14, Bool.true_and]

theorem psd2 : (List.range 6).all (psdRow Data.low Data.high Data.block2) = true := by
  change (psdRow Data.low Data.high Data.block2 0 && (psdRow Data.low Data.high Data.block2 1 && (psdRow Data.low Data.high Data.block2 2 && (psdRow Data.low Data.high Data.block2 3 && (psdRow Data.low Data.high Data.block2 4 && (psdRow Data.low Data.high Data.block2 5 && true)))))) = true
  simp only [psd2_0, psd2_1, psd2_2, psd2_3, psd2_4, psd2_5, Bool.true_and]

theorem expanded2 : (List.range 15).all (expandedRow Data.block2) = true := by
  change (expandedRow Data.block2 0 && (expandedRow Data.block2 1 && (expandedRow Data.block2 2 && (expandedRow Data.block2 3 && (expandedRow Data.block2 4 && (expandedRow Data.block2 5 && (expandedRow Data.block2 6 && (expandedRow Data.block2 7 && (expandedRow Data.block2 8 && (expandedRow Data.block2 9 && (expandedRow Data.block2 10 && (expandedRow Data.block2 11 && (expandedRow Data.block2 12 && (expandedRow Data.block2 13 && (expandedRow Data.block2 14 && true))))))))))))))) = true
  simp only [expanded2_0, expanded2_1, expanded2_2, expanded2_3, expanded2_4, expanded2_5, expanded2_6, expanded2_7, expanded2_8, expanded2_9, expanded2_10, expanded2_11, expanded2_12, expanded2_13, expanded2_14, Bool.true_and]

theorem psd3 : (List.range 20).all (psdRow Data.low Data.high Data.block3) = true := by
  change (psdRow Data.low Data.high Data.block3 0 && (psdRow Data.low Data.high Data.block3 1 && (psdRow Data.low Data.high Data.block3 2 && (psdRow Data.low Data.high Data.block3 3 && (psdRow Data.low Data.high Data.block3 4 && (psdRow Data.low Data.high Data.block3 5 && (psdRow Data.low Data.high Data.block3 6 && (psdRow Data.low Data.high Data.block3 7 && (psdRow Data.low Data.high Data.block3 8 && (psdRow Data.low Data.high Data.block3 9 && (psdRow Data.low Data.high Data.block3 10 && (psdRow Data.low Data.high Data.block3 11 && (psdRow Data.low Data.high Data.block3 12 && (psdRow Data.low Data.high Data.block3 13 && (psdRow Data.low Data.high Data.block3 14 && (psdRow Data.low Data.high Data.block3 15 && (psdRow Data.low Data.high Data.block3 16 && (psdRow Data.low Data.high Data.block3 17 && (psdRow Data.low Data.high Data.block3 18 && (psdRow Data.low Data.high Data.block3 19 && true)))))))))))))))))))) = true
  simp only [psd3_0, psd3_1, psd3_2, psd3_3, psd3_4, psd3_5, psd3_6, psd3_7, psd3_8, psd3_9, psd3_10, psd3_11, psd3_12, psd3_13, psd3_14, psd3_15, psd3_16, psd3_17, psd3_18, psd3_19, Bool.true_and]

theorem expanded3 : (List.range 27).all (expandedRow Data.block3) = true := by
  change (expandedRow Data.block3 0 && (expandedRow Data.block3 1 && (expandedRow Data.block3 2 && (expandedRow Data.block3 3 && (expandedRow Data.block3 4 && (expandedRow Data.block3 5 && (expandedRow Data.block3 6 && (expandedRow Data.block3 7 && (expandedRow Data.block3 8 && (expandedRow Data.block3 9 && (expandedRow Data.block3 10 && (expandedRow Data.block3 11 && (expandedRow Data.block3 12 && (expandedRow Data.block3 13 && (expandedRow Data.block3 14 && (expandedRow Data.block3 15 && (expandedRow Data.block3 16 && (expandedRow Data.block3 17 && (expandedRow Data.block3 18 && (expandedRow Data.block3 19 && (expandedRow Data.block3 20 && (expandedRow Data.block3 21 && (expandedRow Data.block3 22 && (expandedRow Data.block3 23 && (expandedRow Data.block3 24 && (expandedRow Data.block3 25 && (expandedRow Data.block3 26 && true))))))))))))))))))))))))))) = true
  simp only [expanded3_0, expanded3_1, expanded3_2, expanded3_3, expanded3_4, expanded3_5, expanded3_6, expanded3_7, expanded3_8, expanded3_9, expanded3_10, expanded3_11, expanded3_12, expanded3_13, expanded3_14, expanded3_15, expanded3_16, expanded3_17, expanded3_18, expanded3_19, expanded3_20, expanded3_21, expanded3_22, expanded3_23, expanded3_24, expanded3_25, expanded3_26, Bool.true_and]

theorem psd4 : (List.range 18).all (psdRow Data.low Data.high Data.block4) = true := by
  change (psdRow Data.low Data.high Data.block4 0 && (psdRow Data.low Data.high Data.block4 1 && (psdRow Data.low Data.high Data.block4 2 && (psdRow Data.low Data.high Data.block4 3 && (psdRow Data.low Data.high Data.block4 4 && (psdRow Data.low Data.high Data.block4 5 && (psdRow Data.low Data.high Data.block4 6 && (psdRow Data.low Data.high Data.block4 7 && (psdRow Data.low Data.high Data.block4 8 && (psdRow Data.low Data.high Data.block4 9 && (psdRow Data.low Data.high Data.block4 10 && (psdRow Data.low Data.high Data.block4 11 && (psdRow Data.low Data.high Data.block4 12 && (psdRow Data.low Data.high Data.block4 13 && (psdRow Data.low Data.high Data.block4 14 && (psdRow Data.low Data.high Data.block4 15 && (psdRow Data.low Data.high Data.block4 16 && (psdRow Data.low Data.high Data.block4 17 && true)))))))))))))))))) = true
  simp only [psd4_0, psd4_1, psd4_2, psd4_3, psd4_4, psd4_5, psd4_6, psd4_7, psd4_8, psd4_9, psd4_10, psd4_11, psd4_12, psd4_13, psd4_14, psd4_15, psd4_16, psd4_17, Bool.true_and]

theorem expanded4 : (List.range 19).all (expandedRow Data.block4) = true := by
  change (expandedRow Data.block4 0 && (expandedRow Data.block4 1 && (expandedRow Data.block4 2 && (expandedRow Data.block4 3 && (expandedRow Data.block4 4 && (expandedRow Data.block4 5 && (expandedRow Data.block4 6 && (expandedRow Data.block4 7 && (expandedRow Data.block4 8 && (expandedRow Data.block4 9 && (expandedRow Data.block4 10 && (expandedRow Data.block4 11 && (expandedRow Data.block4 12 && (expandedRow Data.block4 13 && (expandedRow Data.block4 14 && (expandedRow Data.block4 15 && (expandedRow Data.block4 16 && (expandedRow Data.block4 17 && (expandedRow Data.block4 18 && true))))))))))))))))))) = true
  simp only [expanded4_0, expanded4_1, expanded4_2, expanded4_3, expanded4_4, expanded4_5, expanded4_6, expanded4_7, expanded4_8, expanded4_9, expanded4_10, expanded4_11, expanded4_12, expanded4_13, expanded4_14, expanded4_15, expanded4_16, expanded4_17, expanded4_18, Bool.true_and]

theorem psd5 : (List.range 15).all (psdRow Data.low Data.high Data.block5) = true := by
  change (psdRow Data.low Data.high Data.block5 0 && (psdRow Data.low Data.high Data.block5 1 && (psdRow Data.low Data.high Data.block5 2 && (psdRow Data.low Data.high Data.block5 3 && (psdRow Data.low Data.high Data.block5 4 && (psdRow Data.low Data.high Data.block5 5 && (psdRow Data.low Data.high Data.block5 6 && (psdRow Data.low Data.high Data.block5 7 && (psdRow Data.low Data.high Data.block5 8 && (psdRow Data.low Data.high Data.block5 9 && (psdRow Data.low Data.high Data.block5 10 && (psdRow Data.low Data.high Data.block5 11 && (psdRow Data.low Data.high Data.block5 12 && (psdRow Data.low Data.high Data.block5 13 && (psdRow Data.low Data.high Data.block5 14 && true))))))))))))))) = true
  simp only [psd5_0, psd5_1, psd5_2, psd5_3, psd5_4, psd5_5, psd5_6, psd5_7, psd5_8, psd5_9, psd5_10, psd5_11, psd5_12, psd5_13, psd5_14, Bool.true_and]

theorem expanded5 : (List.range 20).all (expandedRow Data.block5) = true := by
  change (expandedRow Data.block5 0 && (expandedRow Data.block5 1 && (expandedRow Data.block5 2 && (expandedRow Data.block5 3 && (expandedRow Data.block5 4 && (expandedRow Data.block5 5 && (expandedRow Data.block5 6 && (expandedRow Data.block5 7 && (expandedRow Data.block5 8 && (expandedRow Data.block5 9 && (expandedRow Data.block5 10 && (expandedRow Data.block5 11 && (expandedRow Data.block5 12 && (expandedRow Data.block5 13 && (expandedRow Data.block5 14 && (expandedRow Data.block5 15 && (expandedRow Data.block5 16 && (expandedRow Data.block5 17 && (expandedRow Data.block5 18 && (expandedRow Data.block5 19 && true)))))))))))))))))))) = true
  simp only [expanded5_0, expanded5_1, expanded5_2, expanded5_3, expanded5_4, expanded5_5, expanded5_6, expanded5_7, expanded5_8, expanded5_9, expanded5_10, expanded5_11, expanded5_12, expanded5_13, expanded5_14, expanded5_15, expanded5_16, expanded5_17, expanded5_18, expanded5_19, Bool.true_and]

theorem endpoints : Data.patterns.toList.all Data.endpointOk = true := by
  change (Data.endpointOk Data.patterns[0]! && (Data.endpointOk Data.patterns[1]! && (Data.endpointOk Data.patterns[2]! && (Data.endpointOk Data.patterns[3]! && (Data.endpointOk Data.patterns[4]! && (Data.endpointOk Data.patterns[5]! && (Data.endpointOk Data.patterns[6]! && (Data.endpointOk Data.patterns[7]! && (Data.endpointOk Data.patterns[8]! && (Data.endpointOk Data.patterns[9]! && (Data.endpointOk Data.patterns[10]! && (Data.endpointOk Data.patterns[11]! && (Data.endpointOk Data.patterns[12]! && (Data.endpointOk Data.patterns[13]! && (Data.endpointOk Data.patterns[14]! && (Data.endpointOk Data.patterns[15]! && (Data.endpointOk Data.patterns[16]! && (Data.endpointOk Data.patterns[17]! && (Data.endpointOk Data.patterns[18]! && (Data.endpointOk Data.patterns[19]! && (Data.endpointOk Data.patterns[20]! && (Data.endpointOk Data.patterns[21]! && (Data.endpointOk Data.patterns[22]! && (Data.endpointOk Data.patterns[23]! && (Data.endpointOk Data.patterns[24]! && (Data.endpointOk Data.patterns[25]! && (Data.endpointOk Data.patterns[26]! && (Data.endpointOk Data.patterns[27]! && (Data.endpointOk Data.patterns[28]! && (Data.endpointOk Data.patterns[29]! && (Data.endpointOk Data.patterns[30]! && (Data.endpointOk Data.patterns[31]! && (Data.endpointOk Data.patterns[32]! && (Data.endpointOk Data.patterns[33]! && (Data.endpointOk Data.patterns[34]! && (Data.endpointOk Data.patterns[35]! && (Data.endpointOk Data.patterns[36]! && (Data.endpointOk Data.patterns[37]! && (Data.endpointOk Data.patterns[38]! && (Data.endpointOk Data.patterns[39]! && (Data.endpointOk Data.patterns[40]! && (Data.endpointOk Data.patterns[41]! && (Data.endpointOk Data.patterns[42]! && (Data.endpointOk Data.patterns[43]! && (Data.endpointOk Data.patterns[44]! && (Data.endpointOk Data.patterns[45]! && (Data.endpointOk Data.patterns[46]! && (Data.endpointOk Data.patterns[47]! && (Data.endpointOk Data.patterns[48]! && (Data.endpointOk Data.patterns[49]! && (Data.endpointOk Data.patterns[50]! && (Data.endpointOk Data.patterns[51]! && (Data.endpointOk Data.patterns[52]! && (Data.endpointOk Data.patterns[53]! && (Data.endpointOk Data.patterns[54]! && (Data.endpointOk Data.patterns[55]! && (Data.endpointOk Data.patterns[56]! && (Data.endpointOk Data.patterns[57]! && (Data.endpointOk Data.patterns[58]! && (Data.endpointOk Data.patterns[59]! && (Data.endpointOk Data.patterns[60]! && (Data.endpointOk Data.patterns[61]! && (Data.endpointOk Data.patterns[62]! && (Data.endpointOk Data.patterns[63]! && (Data.endpointOk Data.patterns[64]! && (Data.endpointOk Data.patterns[65]! && (Data.endpointOk Data.patterns[66]! && (Data.endpointOk Data.patterns[67]! && (Data.endpointOk Data.patterns[68]! && (Data.endpointOk Data.patterns[69]! && (Data.endpointOk Data.patterns[70]! && (Data.endpointOk Data.patterns[71]! && (Data.endpointOk Data.patterns[72]! && (Data.endpointOk Data.patterns[73]! && (Data.endpointOk Data.patterns[74]! && (Data.endpointOk Data.patterns[75]! && (Data.endpointOk Data.patterns[76]! && (Data.endpointOk Data.patterns[77]! && (Data.endpointOk Data.patterns[78]! && (Data.endpointOk Data.patterns[79]! && (Data.endpointOk Data.patterns[80]! && (Data.endpointOk Data.patterns[81]! && (Data.endpointOk Data.patterns[82]! && (Data.endpointOk Data.patterns[83]! && (Data.endpointOk Data.patterns[84]! && (Data.endpointOk Data.patterns[85]! && (Data.endpointOk Data.patterns[86]! && (Data.endpointOk Data.patterns[87]! && (Data.endpointOk Data.patterns[88]! && (Data.endpointOk Data.patterns[89]! && (Data.endpointOk Data.patterns[90]! && (Data.endpointOk Data.patterns[91]! && (Data.endpointOk Data.patterns[92]! && (Data.endpointOk Data.patterns[93]! && (Data.endpointOk Data.patterns[94]! && (Data.endpointOk Data.patterns[95]! && (Data.endpointOk Data.patterns[96]! && (Data.endpointOk Data.patterns[97]! && (Data.endpointOk Data.patterns[98]! && (Data.endpointOk Data.patterns[99]! && (Data.endpointOk Data.patterns[100]! && (Data.endpointOk Data.patterns[101]! && (Data.endpointOk Data.patterns[102]! && (Data.endpointOk Data.patterns[103]! && (Data.endpointOk Data.patterns[104]! && (Data.endpointOk Data.patterns[105]! && (Data.endpointOk Data.patterns[106]! && (Data.endpointOk Data.patterns[107]! && (Data.endpointOk Data.patterns[108]! && (Data.endpointOk Data.patterns[109]! && (Data.endpointOk Data.patterns[110]! && (Data.endpointOk Data.patterns[111]! && (Data.endpointOk Data.patterns[112]! && (Data.endpointOk Data.patterns[113]! && (Data.endpointOk Data.patterns[114]! && (Data.endpointOk Data.patterns[115]! && (Data.endpointOk Data.patterns[116]! && (Data.endpointOk Data.patterns[117]! && (Data.endpointOk Data.patterns[118]! && (Data.endpointOk Data.patterns[119]! && (Data.endpointOk Data.patterns[120]! && (Data.endpointOk Data.patterns[121]! && (Data.endpointOk Data.patterns[122]! && (Data.endpointOk Data.patterns[123]! && (Data.endpointOk Data.patterns[124]! && (Data.endpointOk Data.patterns[125]! && (Data.endpointOk Data.patterns[126]! && (Data.endpointOk Data.patterns[127]! && (Data.endpointOk Data.patterns[128]! && (Data.endpointOk Data.patterns[129]! && (Data.endpointOk Data.patterns[130]! && (Data.endpointOk Data.patterns[131]! && (Data.endpointOk Data.patterns[132]! && (Data.endpointOk Data.patterns[133]! && (Data.endpointOk Data.patterns[134]! && (Data.endpointOk Data.patterns[135]! && (Data.endpointOk Data.patterns[136]! && (Data.endpointOk Data.patterns[137]! && (Data.endpointOk Data.patterns[138]! && (Data.endpointOk Data.patterns[139]! && (Data.endpointOk Data.patterns[140]! && (Data.endpointOk Data.patterns[141]! && (Data.endpointOk Data.patterns[142]! && (Data.endpointOk Data.patterns[143]! && (Data.endpointOk Data.patterns[144]! && (Data.endpointOk Data.patterns[145]! && (Data.endpointOk Data.patterns[146]! && (Data.endpointOk Data.patterns[147]! && (Data.endpointOk Data.patterns[148]! && (Data.endpointOk Data.patterns[149]! && (Data.endpointOk Data.patterns[150]! && (Data.endpointOk Data.patterns[151]! && (Data.endpointOk Data.patterns[152]! && (Data.endpointOk Data.patterns[153]! && (Data.endpointOk Data.patterns[154]! && (Data.endpointOk Data.patterns[155]! && (Data.endpointOk Data.patterns[156]! && (Data.endpointOk Data.patterns[157]! && (Data.endpointOk Data.patterns[158]! && (Data.endpointOk Data.patterns[159]! && (Data.endpointOk Data.patterns[160]! && (Data.endpointOk Data.patterns[161]! && (Data.endpointOk Data.patterns[162]! && (Data.endpointOk Data.patterns[163]! && (Data.endpointOk Data.patterns[164]! && (Data.endpointOk Data.patterns[165]! && (Data.endpointOk Data.patterns[166]! && (Data.endpointOk Data.patterns[167]! && (Data.endpointOk Data.patterns[168]! && (Data.endpointOk Data.patterns[169]! && (Data.endpointOk Data.patterns[170]! && (Data.endpointOk Data.patterns[171]! && (Data.endpointOk Data.patterns[172]! && (Data.endpointOk Data.patterns[173]! && (Data.endpointOk Data.patterns[174]! && (Data.endpointOk Data.patterns[175]! && (Data.endpointOk Data.patterns[176]! && (Data.endpointOk Data.patterns[177]! && (Data.endpointOk Data.patterns[178]! && (Data.endpointOk Data.patterns[179]! && (Data.endpointOk Data.patterns[180]! && (Data.endpointOk Data.patterns[181]! && (Data.endpointOk Data.patterns[182]! && (Data.endpointOk Data.patterns[183]! && (Data.endpointOk Data.patterns[184]! && (Data.endpointOk Data.patterns[185]! && (Data.endpointOk Data.patterns[186]! && (Data.endpointOk Data.patterns[187]! && (Data.endpointOk Data.patterns[188]! && (Data.endpointOk Data.patterns[189]! && (Data.endpointOk Data.patterns[190]! && (Data.endpointOk Data.patterns[191]! && (Data.endpointOk Data.patterns[192]! && (Data.endpointOk Data.patterns[193]! && (Data.endpointOk Data.patterns[194]! && (Data.endpointOk Data.patterns[195]! && (Data.endpointOk Data.patterns[196]! && (Data.endpointOk Data.patterns[197]! && (Data.endpointOk Data.patterns[198]! && (Data.endpointOk Data.patterns[199]! && (Data.endpointOk Data.patterns[200]! && (Data.endpointOk Data.patterns[201]! && (Data.endpointOk Data.patterns[202]! && (Data.endpointOk Data.patterns[203]! && (Data.endpointOk Data.patterns[204]! && (Data.endpointOk Data.patterns[205]! && (Data.endpointOk Data.patterns[206]! && (Data.endpointOk Data.patterns[207]! && (Data.endpointOk Data.patterns[208]! && (Data.endpointOk Data.patterns[209]! && (Data.endpointOk Data.patterns[210]! && (Data.endpointOk Data.patterns[211]! && (Data.endpointOk Data.patterns[212]! && (Data.endpointOk Data.patterns[213]! && (Data.endpointOk Data.patterns[214]! && (Data.endpointOk Data.patterns[215]! && (Data.endpointOk Data.patterns[216]! && (Data.endpointOk Data.patterns[217]! && (Data.endpointOk Data.patterns[218]! && (Data.endpointOk Data.patterns[219]! && (Data.endpointOk Data.patterns[220]! && (Data.endpointOk Data.patterns[221]! && (Data.endpointOk Data.patterns[222]! && (Data.endpointOk Data.patterns[223]! && (Data.endpointOk Data.patterns[224]! && (Data.endpointOk Data.patterns[225]! && (Data.endpointOk Data.patterns[226]! && (Data.endpointOk Data.patterns[227]! && (Data.endpointOk Data.patterns[228]! && (Data.endpointOk Data.patterns[229]! && (Data.endpointOk Data.patterns[230]! && (Data.endpointOk Data.patterns[231]! && (Data.endpointOk Data.patterns[232]! && (Data.endpointOk Data.patterns[233]! && (Data.endpointOk Data.patterns[234]! && (Data.endpointOk Data.patterns[235]! && (Data.endpointOk Data.patterns[236]! && (Data.endpointOk Data.patterns[237]! && (Data.endpointOk Data.patterns[238]! && (Data.endpointOk Data.patterns[239]! && (Data.endpointOk Data.patterns[240]! && (Data.endpointOk Data.patterns[241]! && (Data.endpointOk Data.patterns[242]! && (Data.endpointOk Data.patterns[243]! && (Data.endpointOk Data.patterns[244]! && (Data.endpointOk Data.patterns[245]! && (Data.endpointOk Data.patterns[246]! && (Data.endpointOk Data.patterns[247]! && (Data.endpointOk Data.patterns[248]! && (Data.endpointOk Data.patterns[249]! && (Data.endpointOk Data.patterns[250]! && (Data.endpointOk Data.patterns[251]! && (Data.endpointOk Data.patterns[252]! && (Data.endpointOk Data.patterns[253]! && (Data.endpointOk Data.patterns[254]! && (Data.endpointOk Data.patterns[255]! && (Data.endpointOk Data.patterns[256]! && (Data.endpointOk Data.patterns[257]! && (Data.endpointOk Data.patterns[258]! && (Data.endpointOk Data.patterns[259]! && (Data.endpointOk Data.patterns[260]! && (Data.endpointOk Data.patterns[261]! && (Data.endpointOk Data.patterns[262]! && (Data.endpointOk Data.patterns[263]! && (Data.endpointOk Data.patterns[264]! && (Data.endpointOk Data.patterns[265]! && (Data.endpointOk Data.patterns[266]! && (Data.endpointOk Data.patterns[267]! && (Data.endpointOk Data.patterns[268]! && (Data.endpointOk Data.patterns[269]! && (Data.endpointOk Data.patterns[270]! && (Data.endpointOk Data.patterns[271]! && (Data.endpointOk Data.patterns[272]! && (Data.endpointOk Data.patterns[273]! && (Data.endpointOk Data.patterns[274]! && (Data.endpointOk Data.patterns[275]! && (Data.endpointOk Data.patterns[276]! && (Data.endpointOk Data.patterns[277]! && (Data.endpointOk Data.patterns[278]! && (Data.endpointOk Data.patterns[279]! && (Data.endpointOk Data.patterns[280]! && (Data.endpointOk Data.patterns[281]! && (Data.endpointOk Data.patterns[282]! && (Data.endpointOk Data.patterns[283]! && (Data.endpointOk Data.patterns[284]! && (Data.endpointOk Data.patterns[285]! && (Data.endpointOk Data.patterns[286]! && (Data.endpointOk Data.patterns[287]! && (Data.endpointOk Data.patterns[288]! && (Data.endpointOk Data.patterns[289]! && (Data.endpointOk Data.patterns[290]! && (Data.endpointOk Data.patterns[291]! && (Data.endpointOk Data.patterns[292]! && (Data.endpointOk Data.patterns[293]! && (Data.endpointOk Data.patterns[294]! && (Data.endpointOk Data.patterns[295]! && (Data.endpointOk Data.patterns[296]! && (Data.endpointOk Data.patterns[297]! && (Data.endpointOk Data.patterns[298]! && (Data.endpointOk Data.patterns[299]! && (Data.endpointOk Data.patterns[300]! && (Data.endpointOk Data.patterns[301]! && (Data.endpointOk Data.patterns[302]! && (Data.endpointOk Data.patterns[303]! && (Data.endpointOk Data.patterns[304]! && (Data.endpointOk Data.patterns[305]! && (Data.endpointOk Data.patterns[306]! && true))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = true
  simp only [endpoints_0, endpoints_1, endpoints_2, endpoints_3, endpoints_4, endpoints_5, endpoints_6, endpoints_7, endpoints_8, endpoints_9, endpoints_10, endpoints_11, endpoints_12, endpoints_13, endpoints_14, endpoints_15, endpoints_16, endpoints_17, endpoints_18, endpoints_19, endpoints_20, endpoints_21, endpoints_22, endpoints_23, endpoints_24, endpoints_25, endpoints_26, endpoints_27, endpoints_28, endpoints_29, endpoints_30, endpoints_31, endpoints_32, endpoints_33, endpoints_34, endpoints_35, endpoints_36, endpoints_37, endpoints_38, endpoints_39, endpoints_40, endpoints_41, endpoints_42, endpoints_43, endpoints_44, endpoints_45, endpoints_46, endpoints_47, endpoints_48, endpoints_49, endpoints_50, endpoints_51, endpoints_52, endpoints_53, endpoints_54, endpoints_55, endpoints_56, endpoints_57, endpoints_58, endpoints_59, endpoints_60, endpoints_61, endpoints_62, endpoints_63, endpoints_64, endpoints_65, endpoints_66, endpoints_67, endpoints_68, endpoints_69, endpoints_70, endpoints_71, endpoints_72, endpoints_73, endpoints_74, endpoints_75, endpoints_76, endpoints_77, endpoints_78, endpoints_79, endpoints_80, endpoints_81, endpoints_82, endpoints_83, endpoints_84, endpoints_85, endpoints_86, endpoints_87, endpoints_88, endpoints_89, endpoints_90, endpoints_91, endpoints_92, endpoints_93, endpoints_94, endpoints_95, endpoints_96, endpoints_97, endpoints_98, endpoints_99, endpoints_100, endpoints_101, endpoints_102, endpoints_103, endpoints_104, endpoints_105, endpoints_106, endpoints_107, endpoints_108, endpoints_109, endpoints_110, endpoints_111, endpoints_112, endpoints_113, endpoints_114, endpoints_115, endpoints_116, endpoints_117, endpoints_118, endpoints_119, endpoints_120, endpoints_121, endpoints_122, endpoints_123, endpoints_124, endpoints_125, endpoints_126, endpoints_127, endpoints_128, endpoints_129, endpoints_130, endpoints_131, endpoints_132, endpoints_133, endpoints_134, endpoints_135, endpoints_136, endpoints_137, endpoints_138, endpoints_139, endpoints_140, endpoints_141, endpoints_142, endpoints_143, endpoints_144, endpoints_145, endpoints_146, endpoints_147, endpoints_148, endpoints_149, endpoints_150, endpoints_151, endpoints_152, endpoints_153, endpoints_154, endpoints_155, endpoints_156, endpoints_157, endpoints_158, endpoints_159, endpoints_160, endpoints_161, endpoints_162, endpoints_163, endpoints_164, endpoints_165, endpoints_166, endpoints_167, endpoints_168, endpoints_169, endpoints_170, endpoints_171, endpoints_172, endpoints_173, endpoints_174, endpoints_175, endpoints_176, endpoints_177, endpoints_178, endpoints_179, endpoints_180, endpoints_181, endpoints_182, endpoints_183, endpoints_184, endpoints_185, endpoints_186, endpoints_187, endpoints_188, endpoints_189, endpoints_190, endpoints_191, endpoints_192, endpoints_193, endpoints_194, endpoints_195, endpoints_196, endpoints_197, endpoints_198, endpoints_199, endpoints_200, endpoints_201, endpoints_202, endpoints_203, endpoints_204, endpoints_205, endpoints_206, endpoints_207, endpoints_208, endpoints_209, endpoints_210, endpoints_211, endpoints_212, endpoints_213, endpoints_214, endpoints_215, endpoints_216, endpoints_217, endpoints_218, endpoints_219, endpoints_220, endpoints_221, endpoints_222, endpoints_223, endpoints_224, endpoints_225, endpoints_226, endpoints_227, endpoints_228, endpoints_229, endpoints_230, endpoints_231, endpoints_232, endpoints_233, endpoints_234, endpoints_235, endpoints_236, endpoints_237, endpoints_238, endpoints_239, endpoints_240, endpoints_241, endpoints_242, endpoints_243, endpoints_244, endpoints_245, endpoints_246, endpoints_247, endpoints_248, endpoints_249, endpoints_250, endpoints_251, endpoints_252, endpoints_253, endpoints_254, endpoints_255, endpoints_256, endpoints_257, endpoints_258, endpoints_259, endpoints_260, endpoints_261, endpoints_262, endpoints_263, endpoints_264, endpoints_265, endpoints_266, endpoints_267, endpoints_268, endpoints_269, endpoints_270, endpoints_271, endpoints_272, endpoints_273, endpoints_274, endpoints_275, endpoints_276, endpoints_277, endpoints_278, endpoints_279, endpoints_280, endpoints_281, endpoints_282, endpoints_283, endpoints_284, endpoints_285, endpoints_286, endpoints_287, endpoints_288, endpoints_289, endpoints_290, endpoints_291, endpoints_292, endpoints_293, endpoints_294, endpoints_295, endpoints_296, endpoints_297, endpoints_298, endpoints_299, endpoints_300, endpoints_301, endpoints_302, endpoints_303, endpoints_304, endpoints_305, endpoints_306, Bool.true_and]

end Fast.Five.Checked
