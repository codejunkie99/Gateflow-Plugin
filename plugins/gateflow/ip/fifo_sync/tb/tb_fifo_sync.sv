module tb_fifo_sync;
    parameter int WIDTH = 8;
    parameter int DEPTH = 4;

    logic clk = 0, rst_n = 0;
    logic wr_en, rd_en;
    logic [WIDTH-1:0] wr_data, rd_data;
    logic full, empty;
    int pass_count = 0, fail_count = 0;

    fifo_sync #(.WIDTH(WIDTH), .DEPTH(DEPTH)) u_dut (.*);
    always #5 clk = ~clk;

    task check(string name, logic cond);
        if (!cond) begin $display("FAIL: %s", name); fail_count++; end
        else begin $display("PASS: %s", name); pass_count++; end
    endtask

    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_fifo_sync);
        wr_en = 0; rd_en = 0; wr_data = '0;
        repeat(3) @(posedge clk); rst_n = 1; @(posedge clk);
        check("Empty after reset", empty);
        check("Not full after reset", !full);

        // Write until full
        for (int i = 0; i < DEPTH; i++) begin
            wr_data = i[WIDTH-1:0]; wr_en = 1;
            @(posedge clk);
        end
        wr_en = 0; @(posedge clk);
        check("Full after writing DEPTH items", full);

        // Read all
        rd_en = 1;
        for (int i = 0; i < DEPTH; i++) begin
            check($sformatf("Read data[%0d] = %0d", i, i), rd_data == i[WIDTH-1:0]);
            @(posedge clk);
        end
        rd_en = 0; @(posedge clk);
        check("Empty after reading all", empty);

        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        if (fail_count > 0) $finish(1); else $finish(0);
    end
endmodule
