module spi_master_props (input logic clk, rst_n, cs_n, busy);
    p_cs_busy: assert property (@(posedge clk) disable iff (!rst_n) busy |-> !cs_n);
endmodule
