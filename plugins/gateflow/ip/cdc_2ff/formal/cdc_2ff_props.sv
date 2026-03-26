module cdc_2ff_props (input logic clk, rst_n, async_in, sync_out);
    p_reset: assert property (@(posedge clk) !rst_n |=> sync_out == 0);
endmodule
