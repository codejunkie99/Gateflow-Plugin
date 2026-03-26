module fifo_async_props (input logic wr_clk, wr_rst_n, wr_en, full);
    p_no_overflow: assert property (@(posedge wr_clk) disable iff (!wr_rst_n)
        !(wr_en && full));
endmodule
