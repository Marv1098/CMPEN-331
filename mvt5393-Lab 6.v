`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: The Pennsylvania State University
// Engineer: Marvin Tailor
// 
// Create Date: 12/05/2018 01:10:55 AM
// Design Name: CPU
// Module Name: mvt5393_Lab6
// Project Name:
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module mvt5393_Lab6(clk, InstFetch, InstDecode, InstExe, DataMemory, WriteBack);
    input clk;
    output reg [31:0] InstFetch, InstDecode, InstExe, DataMemory, WriteBack;
    
    wire [31:0] PC_Out, PC_In;                                    // Wire for Program Counter Stage.
    wire [31:0] InstData;                                         // Wire for Program Counter Stage.
    
    wire [5:0] OP, Func;                                          // Wire for IF/ID and Control Unit.
    wire [4:0] RS, RT, RD;                                        // Wire for IF/ID and Control Unit.
    wire [15:0] Address;                                          // Wire for IF/ID and Control Unit.
    
    wire writeReg, Mem2Reg, writeMem, aluIM, RegRT;               // Wire for Instruction Decode Stage
    wire [3:0] aluC;                                              // Wire for Instruction Decode Stage
    wire [4:0] muxOut;                                            // Wire for Instruction Decode Stage
    wire [31:0] data1, data2, signExtend;                         // Wire for Instruction Decode Stage
    
    wire [31:0] QA, QB, aluIMM, EmuxOUT, aluOUT;                  // Wire for Execution Stage
    wire [3:0] EaluC;                                             // Wire for Execution Stage
    wire [4:0] ERegRT;                                            // Wire for Execution Stage
    wire Ewritereg, EMem2Reg, EwriteMem, EaluIMM;                 // Wire for Execution Stage
    
    wire [31:0] MaluOUT, Mqb, DataMEM;                            // Wire for Data Memory Stage
    wire [4:0] MRegRT;                                            // Wire for Data Memory Stage
    wire MwriteREG, Mmem2Reg, MwriteMem;                          // Wire for Data Memory Stage
    
    wire [31:0] WaluOUT, WDataMEM, Wmux_OUT;                      // Wire for Write Back Stage
    wire [4:0] WRegRT;                                            // Wire for Write Back Stage
    wire WwriteREG, Wmem2Reg;                                     // Wire for Write Back Stage
      
    program_counter PC (.NPC(PC_In), .PCOut(PC_Out), .clk(clk));
    adder Adder (.NPCOut(PC_In), .a(PC_Out));
    instruction_memory IM (.address(PC_Out), .InstData(InstData));
    IF_ID if_id (.clk(clk), .InstIn(InstData), .opcode(OP), .func(Func), .rs(RS), .rt(RT), .rd(RD), .address(Address));
    control_unit ControlUnit (.opcode(OP), .func(Func), .write_reg(writeReg), .mem2reg(Mem2Reg), .write_mem(writeMem), .aluimm(aluIM), .aluc(aluC), .regrt(RegRT));
    Mux_regRt mux2to1 (.rd(RD), .rt(RT), .regrt(RegRT), .reg_out(muxOut));
    reg_file RegisterFile (.clk(clk), .rs(RS), .rt(RT), .read_data1(data1), .read_data2(data2), .wwreg(Wmem2Reg), .address(Wmux_OUT), .data(WDataMEM));
    sign_extend SignExtender (.addressIn(Address), .addressOut(signExtend));
    ID_EXE id_exe(.clk(clk), .wreg(writeReg), .mem2reg(Mem2Reg), .write_mem(writeMem), .aluc(aluC), .aluimm(aluIM), .regrt(muxOut), .qa(data1), .qb(data2), .imm(signExtend), .wregOut(Ewritereg), .mem2reg_OUT(EMem2Reg), .write_mem_Out(EwriteMem), .aluc_Out(EaluC), .aluimm_Out(EaluIMM), .regrtOut(ERegRT), .qaOut(QA), .qbOut(QB), .immOut(aluIMM));
    Mux_aluImm Emux2to1 (.qb(QB), .aluImm(aluIMM), .sel_aluImm(EaluIMM), .muxOut(EmuxOUT));
    ALU alu (.qa(QA), .qb(EmuxOUT), .aluC(EaluC), .aluOut(aluOUT));
    EXE_MEM exe_mem (.clk(clk), .write_reg(Ewritereg), .mem2reg(EMem2Reg), .write_mem(EwriteMem), .regRt(ERegRT), .alu(aluOUT), .qb(QB), .write_reg_OUT(MwriteREG), .mem2reg_OUT(Mmem2Reg), .write_mem_OUT(MwriteMem), .regRt_OUT(MRegRT), .aluOUT(MaluOUT), .qb_OUT(Mqb));
    Data_Memory RAM (.address(MaluOUT), .data(Mqb), .write_mem(MwriteMem), .mem_out(DataMEM));
    MEM_WB memory_WB (.clk(clk), .MwriteReg(MwriteREG), .Mmem2reg(Mmem2Reg), .MRegRt(MRegRT), .Malu(MaluOUT), .DataMem(DataMEM), .MwriteReg_OUT(WwriteREG), .Mmem2reg_OUT(Wmem2Reg), .MRegRt_OUT(WRegRT), .Malu_OUT(WaluOUT), .DataMem_OUT(WDataMEM));
    MUX_WB Wmux2to1 (.aluData(WaluOUT), .DMaddr(WDataMEM), .wm2reg(Wmem2Reg), .muxOUT(Wmux_OUT));
    
    always@ (posedge clk) begin
        InstFetch <= InstData;
        InstDecode <= InstFetch;
        InstExe <= InstDecode;
        DataMemory <= InstExe;
        WriteBack <= DataMemory;
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* PROGRAM COUNTER */
module program_counter(NPC, PCOut, clk);
    input clk;
    input [31:0] NPC;
    output reg [31:0] PCOut;
    
    reg [31:0] current_PC;
    
    initial
    begin
        PCOut = 0;
        current_PC = 100;
    end
      
    always@(posedge clk) begin
        current_PC <= NPC;
    end
    
    always@(negedge clk) begin
        PCOut <= current_PC;
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* ADDER */
module adder(NPCOut, a);
    input [31:0] a;
    output reg [31:0] NPCOut;
  
    initial begin
        NPCOut = 0;
    end
    
    always@(a) begin
        NPCOut <= a + 4;
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* INSTRUCTION MEMORY */
module instruction_memory(address, InstData);
    input [31:0] address;
    output reg [31:0] InstData;
    reg [31:0] InstIN [0:511];

    initial begin
        InstIN[32'd100] = 32'h8C220000;
        InstIN[32'd104] = 32'h8C230004;
        InstIN[32'd108] = 32'h8C240008;
        InstIN[32'd112] = 32'h8C25000C;
        InstIN[32'd116] = 32'h004A3020;
    end

    always@(address) begin
        InstData <= InstIN[address];
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* INSTRUCTION FETCH AND INSTRUCTION DECODE LATCH */
module IF_ID(clk, InstIn, opcode, func, rs, rt, rd, address);
    input clk;
    input [31:0] InstIn;
    output reg [5:0] opcode, func; 
    output reg [4:0] rs, rt, rd;
    output reg [15:0] address;
    
    reg [31:0] middle; 
 
   always@(posedge clk) begin 
        middle <= InstIn; 
   end
   
   always@(negedge clk) begin  
        opcode <= middle [31:26];
        rs <= middle [25:21];
        rt <= middle [20:16];
        rd <= middle [15:11];
        func <= middle [5:0];
        address <= middle [15:0];
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* CONTROL UNIT */
module control_unit(opcode, func, write_reg, mem2reg, write_mem, aluimm, aluc, regrt);
    input [5:0] opcode, func;
    output reg write_reg, mem2reg, write_mem, aluimm, regrt;
    output reg [3:0] aluc;

    always@(opcode, func) begin
        case(opcode)
        6'b100011: begin
            write_reg <= 1'b1;
            mem2reg <= 1'b1;
            write_mem <= 1'b0;
            aluc <= 4'b0010;
            aluimm <= 1'b1;
            regrt <= 1'b1;
        end
        
        6'b000000: begin
            case(func)
            6'b100000: begin
                write_reg <= 1'b1;
                mem2reg <= 1'b0;
                write_mem <= 1'b0;
                aluc <= 4'b0010;
                aluimm <= 1'b0;
                regrt <= 1'b0;
            end
        endcase
        end
    endcase
 end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* REGRT MULTIPLEXER */
module Mux_regRt(rd, rt, regrt, reg_out);
    input [4:0] rd, rt; 
    input regrt;
    output reg [4:0] reg_out;
    always@(rd,rt,regrt) begin
        case(regrt)
            1'b1: reg_out <= rt;
            1'b0: reg_out <= rd;
        endcase    
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* REGISTER FILE */
module reg_file(clk, rs, rt, read_data1, read_data2, wwreg, address, data);
    input clk, wwreg;
    input [31:0] address, data;
    input [4:0] rs, rt;
    output reg [31:0] read_data1, read_data2;
    integer i;
    reg [31:0] register [0:31];
    
    initial for(i = 0; i < 32; i = i + 1) begin
        register[i] = 32'h00000000;
    end
    
    always @ (rs, rt) begin
        read_data1 <= register[rs];
        read_data2 <= register[rt];
    end
    
    always @ (wwreg, address, data) begin
        case(wwreg)
            1'b1: register[address] <= data;
        endcase
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* SIGN EXTENDER */
module sign_extend(addressIn, addressOut);
    input [15:0] addressIn;
    output reg [31:0] addressOut;

    always @ (addressIn) begin
        addressOut = {{16{addressIn[15]}}, addressIn};
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* INSTRUCTION DECODE AND EXECUTION */
module ID_EXE(clk, wreg, mem2reg, write_mem, aluc, aluimm, regrt, qa, qb, imm, wregOut, mem2reg_OUT, write_mem_Out, aluc_Out, aluimm_Out, regrtOut, qaOut, qbOut, immOut);
    input clk;
    input [31:0] imm, qa, qb;
    input [3:0] aluc;
    input [4:0] regrt;
    input wreg, mem2reg, write_mem, aluimm;
    
    output reg [31:0] immOut, qaOut, qbOut;
    output reg [3:0] aluc_Out;
    output reg [4:0] regrtOut;
    output reg wregOut, mem2reg_OUT, write_mem_Out, aluimm_Out;
     
    reg [31:0] Data1;
    reg [31:0] Data2;
    reg [31:0] Data3;
    reg [4:0] REGRT;
    reg [3:0] ALUC;
    reg write_reg;
    reg writeMem;
    reg ALUIMM;
    reg MEMtoREG;
    
    always @ (posedge clk) begin
       Data1 <= qa;
       Data2 <= qb;
       Data3 <= imm;
       ALUC <= aluc;
       write_reg <= wreg;
       writeMem <= write_mem;
       ALUIMM <= aluimm;
       REGRT <= regrt;
       MEMtoREG <= mem2reg;
    end
    
    always @ (negedge clk) begin
        qaOut <= Data1;
        qbOut <= Data2;
        immOut <= Data3;
        aluc_Out <= ALUC;
        wregOut <= write_reg;
        write_mem_Out <= writeMem;
        aluimm_Out <= ALUIMM;
        regrtOut <= REGRT;
        mem2reg_OUT <= MEMtoREG;
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* ALU IMMEDIATE MULTIPLEXER */
module Mux_aluImm(qb, aluImm, sel_aluImm, muxOut);
    input [31:0] qb, aluImm;
    input sel_aluImm;
    output reg [31:0] muxOut;
    always@(qb, aluImm, sel_aluImm) begin 
            case(sel_aluImm)
                1'b1: muxOut = aluImm;
                1'b0: muxOut = qb;
            endcase
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* ALU */
module ALU(qa, qb, aluC, aluOut);
    input [31:0] qa, qb;
    input [3:0] aluC;
    output reg [31:0] aluOut;
    always@(qa, qb, aluC) begin
        case(aluC)
            4'b0010: aluOut <= qa + qb;
        endcase
    end          
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* EXECUTION AND DATA MEMORY LATCH */
module EXE_MEM(clk, write_reg, mem2reg, write_mem, regRt, alu, qb, write_reg_OUT, mem2reg_OUT, write_mem_OUT, regRt_OUT, aluOUT, qb_OUT);
    input clk;
    input write_reg, mem2reg, write_mem;
    input [31:0] qb, alu;
    input [4:0] regRt;
    output reg write_reg_OUT, mem2reg_OUT, write_mem_OUT;
    output reg [31:0] qb_OUT, aluOUT;
    output reg [4:0] regRt_OUT;
    
    reg Write_Reg, MEM2REG, Write_Mem;
    reg [4:0] RegRt;
    reg [31:0] QB, ALUOUT;
    
    always @ (posedge clk) begin
         Write_Reg <= write_reg;
         MEM2REG <= mem2reg;
         Write_Mem <= write_mem;
         RegRt <= regRt;
         QB <= qb;
         ALUOUT <= alu;
    end
    
    always @ (negedge clk) begin
        write_reg_OUT <= Write_Reg; 
        mem2reg_OUT <= MEM2REG;
        write_mem_OUT <= Write_Mem;
        regRt_OUT <= RegRt;
        qb_OUT <= QB;
        aluOUT <= ALUOUT;
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* DATA MEMORY */
module Data_Memory(address, data, write_mem, mem_out);
    input [31:0] address, data;
    input write_mem;
    output reg [31:0] mem_out;
    
    reg [31:0] Memory [0:63];
    
    initial
    begin
       Memory[0] = 32'hA00000AA;
       Memory[4] = 32'h10000011;
       Memory[8] = 32'h20000022;
       Memory[12] = 32'h30000033;
       Memory[16] = 32'h40000044;
       Memory[20] = 32'h50000055;
       Memory[24] = 32'h60000066;
       Memory[28] = 32'h70000077;
       Memory[32] = 32'h80000088;
       Memory[36] = 32'h90000099;
    end
    
    always @ (address, write_mem) begin
        case(write_mem)
            1'b0: mem_out <= Memory[address];
        endcase
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* MEMORY AND WRITE BACK LATCH */
module MEM_WB(clk, MwriteReg, Mmem2reg, MRegRt, Malu, DataMem, MwriteReg_OUT, Mmem2reg_OUT, MRegRt_OUT, Malu_OUT, DataMem_OUT);
    input clk;
    input [31:0] Malu, DataMem;
    input [4:0] MRegRt;
    input MwriteReg, Mmem2reg;
    
    output reg [31:0] Malu_OUT, DataMem_OUT;
    output reg [4:0] MRegRt_OUT;
    output reg MwriteReg_OUT, Mmem2reg_OUT;
    
    reg [31:0] ALU, Data_Mem;
    reg [4:0] RegRT;
    reg WReg, Mem2Reg;
    
    always @ (posedge clk) begin
       ALU <= Malu;
       Data_Mem <= DataMem;
       RegRT <= MRegRt;
       WReg <= MwriteReg;
       Mem2Reg <= Mmem2reg; 
    end    
    
    always @ (negedge clk) begin
        Malu_OUT <= ALU;
        DataMem_OUT <= Data_Mem;
        MRegRt_OUT <= RegRT;
        MwriteReg_OUT <= WReg;
        Mmem2reg_OUT <= Mem2Reg;
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* WRITE BACK STAGE MUX */
module MUX_WB(aluData, DMaddr, wm2reg, muxOUT);
    input [31:0] aluData, DMaddr;
    input wm2reg;
    output reg [31:0] muxOUT;
    
    always@(*) begin
        case(wm2reg)
            1'b0: muxOUT <= aluData;
            1'b1: muxOUT <= DMaddr;
        endcase
    end
endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/* Lab 6 Testbench */
`timescale 1ns / 1ps

module mvt5393_Lab6_TB();
    reg clk;
    wire [31:0] IF_tb, ID_tb, Exe_tb, RAM_tb, WB_tb;
    
    always begin
        #5 clk = ~clk;
    end
    
    mvt5393_Lab6 TB_Lab6(.clk(clk), .InstFetch(IF_tb), .InstDecode(ID_tb), .InstExe(Exe_tb), .DataMemory(RAM_tb), .WriteBack(WB_tb));        
        initial begin
            clk = 0;
        end  
endmodule
