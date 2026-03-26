module axi4lite_props (input logic clk, rst_n, awvalid, awready, wvalid, wready, bvalid, bready);
    p_bresp_after_write: assert property (@(posedge clk) disable iff (!rst_n)
        awvalid && awready && wvalid && wready |=> bvalid);
endmodule
