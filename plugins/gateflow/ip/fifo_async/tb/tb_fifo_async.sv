module tb_fifo_async;
    logic wr_clk=0, rd_clk=0, wr_rst_n=0, rd_rst_n=0;
    logic wr_en=0, rd_en=0, full, empty;
    logic [7:0] wr_data, rd_data;
    int pass_count=0, fail_count=0;
    fifo_async #(.WIDTH(8), .DEPTH(4)) u_dut (.*);
    always #5 wr_clk = ~wr_clk;
    always #7 rd_clk = ~rd_clk;
    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_fifo_async);
        repeat(5) @(posedge wr_clk); wr_rst_n = 1; rd_rst_n = 1;
        repeat(3) @(posedge wr_clk);
        // Write 3 items
        for (int i = 0; i < 3; i++) begin
            wr_data = i[7:0]; wr_en = 1; @(posedge wr_clk);
        end
        wr_en = 0;
        repeat(5) @(posedge rd_clk); // wait for sync
        // Read 3 items
        for (int i = 0; i < 3; i++) begin
            rd_en = 1; @(posedge rd_clk);
            if (rd_data === i[7:0]) begin $display("PASS: read %0d", i); pass_count++; end
            else begin $display("FAIL: got %0d exp %0d", rd_data, i); fail_count++; end
        end
        rd_en = 0; @(posedge rd_clk);
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        $finish;
    end
endmodule
