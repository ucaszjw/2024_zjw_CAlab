module mycpu_top(
    input  wire        clk,
    input  wire        resetn,
    // inst sram interface
    output wire        inst_sram_en,
    output wire [ 3:0] inst_sram_we,
    output wire [31:0] inst_sram_addr,
    output wire [31:0] inst_sram_wdata,
    input  wire [31:0] inst_sram_rdata,
    // data sram interface
    output wire        data_sram_en,
    output wire [ 3:0] data_sram_we,
    output wire [31:0] data_sram_addr,
    output wire [31:0] data_sram_wdata,
    input  wire [31:0] data_sram_rdata,
    // trace debug interface
    output wire [31:0] debug_wb_pc,
    output wire [ 3:0] debug_wb_rf_we,
    output wire [ 4:0] debug_wb_rf_wnum,
    output wire [31:0] debug_wb_rf_wdata
);

// Declare signals
reg         reset;
always @(posedge clk) reset <= ~resetn;

wire [31:0] seq_pc; // use in IF stage
wire [31:0] nextpc; // use in IF stage
wire        br_taken;
wire [31:0] br_target;
wire [31:0] inst;
reg  [31:0] pc;

wire [11:0] alu_op; // use in EXE stage
wire        load_op; // use in MEM stage
wire        src1_is_pc; // use in EXE stage
wire        src2_is_imm; // use in EXE stage
wire        res_from_mem; // use in WB stage
wire        dst_is_r1; // use in WB stage
wire        gr_we; // use in WB stage
wire        mem_we; // use in MEM stage
wire        src_reg_is_rd; // use in EXE stage
wire        rj_eq_rd; // use in ID stage
wire [4: 0] dest;
wire [31:0] rj_value;
wire [31:0] rkd_value;
wire [31:0] imm;
wire [31:0] br_offs;
wire [31:0] jirl_offs;

wire [ 5:0] op_31_26;
wire [ 3:0] op_25_22;
wire [ 1:0] op_21_20;
wire [ 4:0] op_19_15;
wire [ 4:0] rd;
wire [ 4:0] rj;
wire [ 4:0] rk;
wire [11:0] i12;
wire [19:0] i20;
wire [15:0] i16;
wire [25:0] i26;

wire [63:0] op_31_26_d;
wire [15:0] op_25_22_d;
wire [ 3:0] op_21_20_d;
wire [31:0] op_19_15_d;

wire        inst_add_w;
wire        inst_sub_w;
wire        inst_slt;
wire        inst_sltu;
wire        inst_nor;
wire        inst_and;
wire        inst_or;
wire        inst_xor;
wire        inst_slli_w;
wire        inst_srli_w;
wire        inst_srai_w;
wire        inst_addi_w;
wire        inst_ld_w;
wire        inst_st_w;
wire        inst_jirl;
wire        inst_b;
wire        inst_bl;
wire        inst_beq;
wire        inst_bne;
wire        inst_lu12i_w;

wire        need_ui5;
wire        need_si12;
wire        need_si16;
wire        need_si20;
wire        need_si26;
wire        src2_is_4;

wire [ 4:0] rf_raddr1;
wire [31:0] rf_rdata1;
wire [ 4:0] rf_raddr2;
wire [31:0] rf_rdata2;
wire        rf_we   ;
wire [ 4:0] rf_waddr;
wire [31:0] rf_wdata;

wire [31:0] alu_src1   ;
wire [31:0] alu_src2   ;
wire [31:0] alu_result ;

wire [31:0] mem_result;
wire [31:0] final_result;


// IF stage
reg    if_valid;
wire   if_allowin;
wire   if_readygo;
wire   if_pass;
always @(posedge clk) begin
    if (reset) begin
        if_valid <= 1'b0;
    end
    else if (if_allowin) begin
        if_valid <= 1'b1;
    end
    else if (br_taken_cancel) begin
        if_valid <= 1'b0;
    end
end
assign if_allowin = ~if_valid | id_allowin & if_readygo;
assign if_readygo = 1'b1;
assign if_pass    = if_valid & if_readygo;

assign seq_pc       = pc + 3'h4;
assign nextpc       = br_taken_cancel ? br_target : seq_pc;

always @(posedge clk) begin
    if (reset) begin
        pc <= 32'h1bfffffc;     //trick: to make nextpc be 0x1c000000 during reset 
    end
    else if (if_allowin) begin
        pc <= nextpc;
    end
end

assign inst_sram_en    = if_allowin;
assign inst_sram_we    = 4'b0;
assign inst_sram_addr  = nextpc;
assign inst_sram_wdata = 32'b0;
assign inst            = inst_sram_rdata;


// IF --> ID
reg [31:0] inst_id;
reg [31:0] pc_id;
always @(posedge clk) begin
    if (if_pass & id_allowin) begin
        inst_id <= inst;
        pc_id   <= pc;
    end
end


// ID stage
reg     id_valid;
wire    id_allowin;
wire    id_readygo;
wire    id_pass;
wire    inst_src_is_r1;
wire    inst_src_is_r2;
wire    br_taken_cancel;
always @(posedge clk) begin
    if (reset) begin
        id_valid <= 1'b0;
    end
    else if (br_taken_cancel) begin
        id_valid <= 1'b0;
    end
    else if (id_allowin) begin
        id_valid <= if_pass;
    end
end
assign id_allowin = ~id_valid | exe_allowin & id_pass;
// assign id_readygo = ~(gr_we_exe & exe_valid & (inst_src_is_r1 & (rf_raddr1 == dest_exe) 
//                                              | inst_src_is_r2 & (rf_raddr2 == dest_exe))
//                     | gr_we_mem & mem_valid & (inst_src_is_r1 & (rf_raddr1 == dest_mem) 
//                                              | inst_src_is_r2 & (rf_raddr2 == dest_mem))
//                     | gr_we_wb  &  wb_valid & (inst_src_is_r1 & (rf_raddr1 == dest_wb)  
//                                              | inst_src_is_r2 & (rf_raddr2 == dest_wb)));
// assign inst_src_is_r1 = inst_add_w | inst_sub_w | inst_slt | inst_sltu 
//                       | inst_nor | inst_and | inst_or | inst_xor
//                       | inst_slli_w | inst_srli_w | inst_srai_w | inst_addi_w
//                       | inst_ld_w | inst_st_w | inst_beq | inst_bne | inst_jirl;

// assign inst_src_is_r2 = inst_add_w | inst_sub_w | inst_slt | inst_sltu
//                       | inst_nor | inst_and | inst_or | inst_xor
//                       | inst_beq | inst_bne | inst_st_w;
assign id_readygo = ~((rf_raddr1 == dest_exe | rf_raddr2 == dest_exe) && ld_w_exe) | ~exe_valid;
assign id_pass    = id_valid & id_readygo;

assign op_31_26  = inst_id[31:26];
assign op_25_22  = inst_id[25:22];
assign op_21_20  = inst_id[21:20];
assign op_19_15  = inst_id[19:15];

assign rd   = inst_id[ 4: 0];
assign rj   = inst_id[ 9: 5];
assign rk   = inst_id[14:10];

assign i12  = inst_id[21:10];
assign i20  = inst_id[24: 5];
assign i16  = inst_id[25:10];
assign i26  = {inst_id[ 9: 0], inst_id[25:10]};

decoder_6_64 u_dec0(.in(op_31_26 ), .out(op_31_26_d ));
decoder_4_16 u_dec1(.in(op_25_22 ), .out(op_25_22_d ));
decoder_2_4  u_dec2(.in(op_21_20 ), .out(op_21_20_d ));
decoder_5_32 u_dec3(.in(op_19_15 ), .out(op_19_15_d ));

assign inst_add_w  = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h00];
assign inst_sub_w  = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h02];
assign inst_slt    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h04];
assign inst_sltu   = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h05];
assign inst_nor    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h08];
assign inst_and    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h09];
assign inst_or     = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0a];
assign inst_xor    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0b];
assign inst_slli_w = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h01];
assign inst_srli_w = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h09];
assign inst_srai_w = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h11];
assign inst_addi_w = op_31_26_d[6'h00] & op_25_22_d[4'ha];
assign inst_ld_w   = op_31_26_d[6'h0a] & op_25_22_d[4'h2];
assign inst_st_w   = op_31_26_d[6'h0a] & op_25_22_d[4'h6];
assign inst_jirl   = op_31_26_d[6'h13];
assign inst_b      = op_31_26_d[6'h14];
assign inst_bl     = op_31_26_d[6'h15];
assign inst_beq    = op_31_26_d[6'h16];
assign inst_bne    = op_31_26_d[6'h17];
assign inst_lu12i_w= op_31_26_d[6'h05] & ~inst_id[25];

assign alu_op[ 0] = inst_add_w | inst_addi_w | inst_ld_w | inst_st_w
                    | inst_jirl | inst_bl;
assign alu_op[ 1] = inst_sub_w;
assign alu_op[ 2] = inst_slt;
assign alu_op[ 3] = inst_sltu;
assign alu_op[ 4] = inst_and;
assign alu_op[ 5] = inst_nor;
assign alu_op[ 6] = inst_or;
assign alu_op[ 7] = inst_xor;
assign alu_op[ 8] = inst_slli_w;
assign alu_op[ 9] = inst_srli_w;
assign alu_op[10] = inst_srai_w;
assign alu_op[11] = inst_lu12i_w;

assign need_ui5   =  inst_slli_w | inst_srli_w | inst_srai_w;
assign need_si12  =  inst_addi_w | inst_ld_w | inst_st_w;
assign need_si16  =  inst_jirl | inst_beq | inst_bne;
assign need_si20  =  inst_lu12i_w;
assign need_si26  =  inst_b | inst_bl;
assign src2_is_4  =  inst_jirl | inst_bl;

assign imm = src2_is_4 ? 32'h4                      :
             need_si20 ? {i20[19:0], 12'b0}         :
                         {{20{i12[11]}}, i12[11:0]} ;

assign br_offs = need_si26 ? {{ 4{i26[25]}}, i26[25:0], 2'b0} :
                             {{14{i16[15]}}, i16[15:0], 2'b0} ;

assign jirl_offs = {{14{i16[15]}}, i16[15:0], 2'b0};

assign src_reg_is_rd = inst_beq | inst_bne | inst_st_w;

assign src1_is_pc    = inst_jirl | inst_bl;

assign src2_is_imm   = inst_slli_w |
                       inst_srli_w |
                       inst_srai_w |
                       inst_addi_w |
                       inst_ld_w   |
                       inst_st_w   |
                       inst_lu12i_w|
                       inst_jirl   |
                       inst_bl     ;

assign res_from_mem  = inst_ld_w;
assign dst_is_r1     = inst_bl;
assign gr_we         = ~inst_st_w & ~inst_beq & ~inst_bne & ~inst_b;
assign mem_we        = inst_st_w;
assign dest          = dst_is_r1 ? 5'd1 : rd;

assign rf_raddr1 = rj;
assign rf_raddr2 = src_reg_is_rd ? rd :rk;
regfile u_regfile(
    .clk    (clk      ),
    .raddr1 (rf_raddr1),
    .rdata1 (rf_rdata1),
    .raddr2 (rf_raddr2),
    .rdata2 (rf_rdata2),
    .we     (rf_we    ),
    .waddr  (rf_waddr ),
    .wdata  (rf_wdata )
);

assign rj_value  = (rf_raddr1 == dest_exe && dest_exe != 5'b0 && gr_we_exe && !ld_w_exe) ? alu_result_forward :
                   (rf_raddr1 == dest_mem && dest_mem != 5'b0 && gr_we_mem) ? res_from_mem_mem ? mem_result_forward : alu_result_mem_forward :
                   (rf_raddr1 == dest_wb  && dest_wb  != 5'b0 && gr_we_wb ) ? final_result_forward :
                                                                              rf_rdata1;

assign rkd_value = (rf_raddr2 == dest_exe && dest_exe != 5'b0 && gr_we_exe && !ld_w_exe) ? alu_result_forward :
                   (rf_raddr2 == dest_mem && dest_mem != 5'b0 && gr_we_mem) ? res_from_mem_mem ? mem_result_forward : alu_result_mem_forward :
                   (rf_raddr2 == dest_wb  && dest_wb  != 5'b0 && gr_we_wb ) ? final_result_forward :
                                                                              rf_rdata2;

assign rj_eq_rd = (rj_value == rkd_value);
assign br_taken = (  inst_beq  &  rj_eq_rd
                   | inst_bne  & !rj_eq_rd
                   | inst_jirl
                   | inst_bl
                   | inst_b
                  ) & id_valid;
assign br_taken_cancel = br_taken & id_readygo;
assign br_target = (inst_beq | inst_bne | inst_bl | inst_b) ? (pc_id + br_offs) :
                                                   /*inst_jirl*/ (rj_value + jirl_offs);


// ID --> EXE
reg [31:0] inst_exe;
reg [31:0] pc_exe;
reg [31:0] alu_op_exe;
reg [ 4:0] dest_exe;
reg [31:0] rj_value_exe;
reg [31:0] rkd_value_exe;
reg [31:0] imm_exe;
reg [31:0] br_offs_exe;
reg [31:0] jirl_offs_exe;
reg        src1_is_pc_exe;
reg        src2_is_imm_exe;
reg        res_from_mem_exe;
reg        dst_is_r1_exe;
reg        gr_we_exe;
reg        mem_we_exe;
reg        ld_w_exe;
always @(posedge clk) begin
    if (reset) begin
        gr_we_exe <= 1'b0;
        dest_exe  <= 5'b0;
        ld_w_exe  <= 1'b0;
    end
    else if (id_pass & exe_allowin) begin
        inst_exe     <= inst_id;
        pc_exe       <= pc_id;
        alu_op_exe   <= alu_op;
        dest_exe     <= dest;
        rj_value_exe <= rj_value;
        rkd_value_exe<= rkd_value;
        imm_exe      <= imm;
        br_offs_exe  <= br_offs;
        jirl_offs_exe<= jirl_offs;
        src1_is_pc_exe<= src1_is_pc;
        src2_is_imm_exe<= src2_is_imm;
        res_from_mem_exe<= res_from_mem;
        dst_is_r1_exe<= dst_is_r1;
        gr_we_exe    <= gr_we;
        mem_we_exe   <= mem_we;
        ld_w_exe     <= inst_ld_w;
    end
end

// EXE stage
reg    exe_valid;
wire   exe_allowin;
wire   exe_readygo;
wire   exe_pass;
wire [31:0] alu_result_forward;
always @(posedge clk) begin
    if (reset) begin
        exe_valid <= 1'b0;
    end
    else begin
        exe_valid <= id_pass & exe_allowin;
    end
end
assign exe_allowin = ~exe_valid | mem_allowin & exe_pass;
assign exe_readygo = 1'b1;
assign exe_pass    = exe_valid & exe_readygo;

assign alu_src1 = src1_is_pc_exe  ? pc_exe[31:0] : rj_value_exe;
assign alu_src2 = src2_is_imm_exe ? imm_exe : rkd_value_exe;

alu u_alu(
    .alu_op     (alu_op_exe),
    .alu_src1   (alu_src1  ),
    .alu_src2   (alu_src2  ),
    .alu_result (alu_result)
);

assign alu_result_forward = alu_result;


// EXE --> MEM
reg [31:0] alu_result_mem;
reg [31:0] pc_mem;
reg [ 4:0] dest_mem;
reg        gr_we_mem;
reg        res_from_mem_mem;

always @(posedge clk) begin
    if (reset) begin
        gr_we_mem <= 1'b0;
        dest_mem  <= 5'b0;
    end
    else if (exe_pass & mem_allowin) begin
        alu_result_mem         <= alu_result;
        pc_mem                 <= pc_exe;
        dest_mem               <= dest_exe;
        gr_we_mem              <= gr_we_exe;
        res_from_mem_mem       <= res_from_mem_exe;
    end
end

// MEM stage
reg    mem_valid;
wire   mem_allowin;
wire   mem_readygo;
wire   mem_pass;
wire [31:0] mem_result_forward;
wire [31:0] alu_result_mem_forward;


always @(posedge clk) begin
    if (reset) begin
        mem_valid <= 1'b0;
    end
    else begin
        mem_valid <= exe_pass & mem_allowin;
    end
end
assign mem_allowin = ~mem_valid | wb_allowin & mem_pass;
assign mem_readygo = 1'b1;
assign mem_pass    = mem_valid & mem_readygo;

assign data_sram_en    = 1'b1;
assign data_sram_we    = {4{mem_we_exe}};
assign data_sram_addr  = alu_result;
assign data_sram_wdata = rkd_value_exe;

assign mem_result   = data_sram_rdata;
assign mem_result_forward = mem_result;

assign alu_result_mem_forward = alu_result_mem;


// MEM --> WB
reg [31:0] alu_result_wb;
reg [31:0] mem_result_wb;
reg [31:0] pc_wb;
reg [ 4:0] dest_wb;
reg        gr_we_wb;
reg        res_from_mem_wb;

always @(posedge clk) begin
    if (reset) begin
        gr_we_wb <= 1'b0;
        dest_wb  <= 5'b0;
    end
    else if (mem_pass & wb_allowin) begin
        alu_result_wb   <= alu_result_mem;
        mem_result_wb   <= mem_result;
        pc_wb           <= pc_mem;
        dest_wb         <= dest_mem;
        gr_we_wb        <= gr_we_mem;
        res_from_mem_wb <= res_from_mem_mem;
    end
end


// WB stage
reg    wb_valid;
wire   wb_allowin;
wire   wb_readygo;
wire [31:0] final_result_forward;
always @(posedge clk) begin
    if (reset) begin
        wb_valid <= 1'b0;
    end
    else begin
        wb_valid <= mem_pass & wb_allowin;
    end
end
assign wb_allowin = ~wb_valid | wb_readygo;
assign wb_readygo = 1'b1;

assign final_result = res_from_mem_wb ? mem_result_wb : alu_result_wb;
assign final_result_forward = final_result;
assign rf_we    = gr_we_wb & wb_valid;
assign rf_waddr = dest_wb;
assign rf_wdata = final_result;

// debug info generate
assign debug_wb_pc       = pc_wb;
assign debug_wb_rf_we    = {4{rf_we}};
assign debug_wb_rf_wnum  = dest_wb;
assign debug_wb_rf_wdata = final_result;

endmodule