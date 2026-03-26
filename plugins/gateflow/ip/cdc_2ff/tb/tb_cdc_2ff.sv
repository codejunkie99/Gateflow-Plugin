module tb_cdc_2ff;
    logic clk = 0, rst_n = 0, async_in = 0, sync_out;
    int pass_count = 0, fail_count = 0;
    cdc_2ff #(.STAGES(2)) u_dut (.*);
    always #5 clk = ~clk;
    task check(string name, logic expected);
        if (sync_out !== expected) begin $display("FAIL: %s got %b exp %b", name, sync_out, expected); fail_count++; end
        else begin $display("PASS: %s", name); pass_count++; end
    endtask
    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_cdc_2ff);
        repeat(3) @(posedge clk); rst_n = 1; @(posedge clk);
        check("Zero after reset", 1'b0);
        async_in = 1; repeat(3) @(posedge clk);
        check("Synced high after 2+ cycles", 1'b1);
        async_in = 0; repeat(3) @(posedge clk);
        check("Synced low after 2+ cycles", 1'b0);
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        $finish;
    end
endmodule
