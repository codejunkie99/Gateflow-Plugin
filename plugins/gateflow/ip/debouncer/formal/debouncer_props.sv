module debouncer_props (input logic clk, rst_n, btn_out, btn_rise, btn_fall);
    p_edges_one_cycle: assert property (@(posedge clk) disable iff (!rst_n)
        btn_rise |=> !btn_rise);
    p_no_simultaneous: assert property (@(posedge clk) disable iff (!rst_n)
        !(btn_rise && btn_fall));
endmodule
