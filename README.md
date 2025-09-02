# Assertion-Checker-Generator
[Harman] Assertion Checker Generator

RTL Auto Parsing & Excel Editing
-------------------------

<img width="1118" height="326" alt="Image" src="https://github.com/user-attachments/assets/ea501a9a-45a3-43d9-93bc-8caf7922bd50" />
<br>
<div align=center>
RTL Auto Parsing 실행 예시
</div>

<br><br>
검증 대상이 될 RTL을 물리면 상위 폴더로 올라가면서 .v파일들을 탐색하고 계층 분석을 통해 검증될 Target Block의 Instanse 정보를 JSON으로 저장한다.
저장되는 정보는
**Top path, module, instance name, clock, reset, input, output, inout, parameter**가 있다.
<br>
  
**TOP Path :** Parsing 이외에 사용자가 입력해 주는 Path이다. 
예를들어 SVA검증 대상 경로가 top.dut.WRAPPER_BLK_ABC.blk_abc.u_module_a.u_sub_module_b 라고 했을 때, parsing의 결과가 blk_abc.u_module_a.u_sub_module_b인 경우 TOP Path입력을top.dut.WRAPPER_BLK_ABC.blk_abc.u_module_a와 같이 입력한다면, top.dut.WRAPPER_BLK_ABC.blk_abc.u_module_a는 `TOP_PATH 로 local define되고 Checker Interface 내부에는 `TOP_PATH.u_sub_module_b나 `TOP_PATH.u_sub_module_b.i_clk 와 같이 짧은 경로가 사용되어 가독성을 향상 시킬 수 있다.
<br><br>
**module :** 검증 대상이 된 instance의 module name 원형이다.

**paths :** 검증 대상이 된 instance의 TOP_PATH 부분을 제외한 RTL Path이다. 만약 한 module안에 검증해야할 같은 구조의 module들이 있다면 한꺼번에 SVA Checker생성이 가능하도록 여러 path를 list로 받아 저장할 수 있도록 하였다. 여러개의 instance를 받은 경우 같은 내부 포트 정보를 공유하므로 path 정보만 교체하면서 각각의 input에 대해 같은 목적의 Checker를 활용하여 검증이 가능하도록 구현 할 예정이다.

**instances :** 검증 대상이 된 instance들의 이름들을 list형식으로 나타낸다.

**clocks :** i_clk, i_sclk, i_aclk, i_CLK, I_CLK, i_clock... 등 여러가지 일반적인 clock naming rule을 따라 clock이라 예상되는 input을 받아 저장한다.

**resets :** i_rst, i_rstn, i_reset, I_RST, i_GRESETn... 등 여러가지 일반적인 reset naming rule을 따라 reset이라 예상되는 input을 받아 저장한다.

**input :** clock과 reset, parameter를 제외한 input들의 이름과 width 정보를 저장한다.

**output :** output port들의 이름과 width 정보를 저장한다.

**inout :** inout port들의 이름과 width 정보를 저장한다.

**parameter :** p_* 인 parameter나 SFR, Register setting 등의 input port를 저장한다.

+ `BIT_WIDTH 와 같은 local param이나 define되어있는 정보는 마찬가지로 목표 instance 내부와 외부에서 탐색하여 현재 설정된 값으로 대체하여 활용한다.
+ 또한, excel로 가져올 때는 bit가 총 몇 비트인지가 중요하기 때문에 [15:0] 같은 값은 16 bits 라고 간소화 하여 불러온다.

<div align=center>
<br><br> 
<center> <img width="485" height="636" alt="Image" src="https://github.com/user-attachments/assets/f456ae8c-8279-4ce7-9314-1a4b70e52475" /> </center>
<br>
출력된 JSON파일
<br> <br>
<img width="447" height="444" alt="Image" src="https://github.com/user-attachments/assets/6d71d4a5-e82d-4200-a6c1-98174c18a8ce" />
<br>엑셀 출력 log
<br> <br>
<img width="1447" height="515" alt="Image" src="https://github.com/user-attachments/assets/7d286dc7-58b5-451a-8483-86d5abdc341c" />
<br>
최종 결과물
<br><br>
</div>
