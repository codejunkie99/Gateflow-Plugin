module tb_spi_master;
    logic clk=0, rst_n=0, start=0, busy, done, sclk, mosi, miso=0, cs_n;
    logic [7:0] tx_data, rx_data;
    int pass_count=0, fail_count=0;
    spi_master #(.CLK_DIV(2), .DATA_WIDTH(8)) u_dut (
        .clk(clk), .rst_n(rst_n), .cpol(1'b0), .cpha(1'b0),
        .tx_data(tx_data), .start(start), .rx_data(rx_data),
        .busy(busy), .done(done), .sclk(sclk), .mosi(mosi), .miso(miso), .cs_n(cs_n)
    );
    always #5 clk = ~clk;
    assign miso = mosi; // loopback
    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_spi_master);
        repeat(3) @(posedge clk); rst_n = 1; @(posedge clk);
        tx_data = 8'hA5; start = 1; @(posedge clk); start = 0;
        wait(done); @(posedge clk);
        if (rx_data === 8'hA5) begin $display("PASS: loopback"); pass_count++; end
        else begin $display("FAIL: got %02h", rx_data); fail_count++; end
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        $finish;
    end
endmodule
