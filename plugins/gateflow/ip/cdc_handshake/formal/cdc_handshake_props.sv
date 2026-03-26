module cdc_handshake_props (input logic src_clk, src_rst_n, src_valid, src_ready);
    p_backpressure: assert property (@(posedge src_clk) disable iff (!src_rst_n)
        src_valid && !src_ready |=> !src_ready || $past(src_ready));
endmodule
