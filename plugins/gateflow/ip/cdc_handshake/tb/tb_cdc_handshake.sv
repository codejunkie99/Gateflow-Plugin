module tb_cdc_handshake;
    logic src_clk=0, dst_clk=0, src_rst_n=0, dst_rst_n=0;
    logic [7:0] src_data, dst_data;
    logic src_valid=0, src_ready, dst_valid;
    int pass_count=0, fail_count=0;
    cdc_handshake #(.WIDTH(8)) u_dut (.*);
    always #5 src_clk = ~src_clk;
    always #7 dst_clk = ~dst_clk;
    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_cdc_handshake);
        repeat(5) @(posedge src_clk); src_rst_n=1; dst_rst_n=1;
        repeat(3) @(posedge src_clk);
        src_data = 8'hAB; src_valid = 1;
        wait(src_ready); @(posedge src_clk); src_valid = 0;
        wait(dst_valid); @(posedge dst_clk);
        if (dst_data === 8'hAB) begin $display("PASS: handshake"); pass_count++; end
        else begin $display("FAIL: %02h", dst_data); fail_count++; end
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        $finish;
    end
endmodule
