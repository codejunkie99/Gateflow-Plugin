module uart_props (input logic clk, rst_n, tx_valid, tx_ready, tx_out);
    p_idle_high: assert property (@(posedge clk) disable iff (!rst_n)
        tx_ready |-> tx_out);
    p_valid_ready: assert property (@(posedge clk) disable iff (!rst_n)
        tx_valid && tx_ready |=> !tx_ready);
endmodule
