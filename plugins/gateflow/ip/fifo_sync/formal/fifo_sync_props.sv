module fifo_sync_props #(parameter int WIDTH = 8, DEPTH = 16) (
    input logic clk, rst_n, wr_en, rd_en, full, empty,
    input logic [$clog2(DEPTH):0] wr_ptr, rd_ptr
);
    // No write when full
    p_no_overflow: assert property (@(posedge clk) disable iff (!rst_n)
        full |-> !wr_en || $past(wr_en && full));

    // No read when empty
    p_no_underflow: assert property (@(posedge clk) disable iff (!rst_n)
        !(rd_en && empty));

    // Pointers consistent
    p_ptr_range: assert property (@(posedge clk) disable iff (!rst_n)
        (wr_ptr - rd_ptr) <= DEPTH);
endmodule
