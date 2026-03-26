module tb_debouncer;
    parameter int CLK_FREQ = 1000, DEBOUNCE_MS = 5;
    logic clk = 0, rst_n = 0, btn_in = 0, btn_out, btn_rise, btn_fall;
    int pass_count = 0, fail_count = 0;
    debouncer #(.CLK_FREQ(CLK_FREQ), .DEBOUNCE_MS(DEBOUNCE_MS)) u_dut (.*);
    always #5 clk = ~clk;
    task check(string name, logic cond);
        if (!cond) begin $display("FAIL: %s", name); fail_count++; end
        else begin $display("PASS: %s", name); pass_count++; end
    endtask
    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_debouncer);
        repeat(3) @(posedge clk); rst_n = 1; @(posedge clk);
        check("Output low after reset", !btn_out);
        // Bounce
        btn_in = 1; repeat(2) @(posedge clk); btn_in = 0; @(posedge clk); btn_in = 1;
        repeat(10) @(posedge clk);
        check("Debounced high", btn_out);
        btn_in = 0; repeat(10) @(posedge clk);
        check("Debounced low", !btn_out);
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        $finish;
    end
endmodule
