module tb_uart;
    parameter int CLK_FREQ = 10_000, BAUD_RATE = 1000;
    logic clk = 0, rst_n = 0;
    logic [7:0] tx_data, rx_data;
    logic tx_valid, tx_ready, tx_out, rx_valid;
    int pass_count = 0, fail_count = 0;

    uart_tx #(.CLK_FREQ(CLK_FREQ), .BAUD_RATE(BAUD_RATE)) u_tx (
        .clk(clk), .rst_n(rst_n), .tx_data(tx_data),
        .tx_valid(tx_valid), .tx_ready(tx_ready), .tx_out(tx_out)
    );
    uart_rx #(.CLK_FREQ(CLK_FREQ), .BAUD_RATE(BAUD_RATE)) u_rx (
        .clk(clk), .rst_n(rst_n), .rx_in(tx_out),
        .rx_data(rx_data), .rx_valid(rx_valid)
    );
    always #5 clk = ~clk;

    task send_byte(input logic [7:0] data);
        @(posedge clk);
        tx_data = data; tx_valid = 1;
        @(posedge clk); tx_valid = 0;
        wait(rx_valid); @(posedge clk);
        if (rx_data === data) begin
            $display("PASS: Sent 0x%02h, received 0x%02h", data, rx_data);
            pass_count++;
        end else begin
            $display("FAIL: Sent 0x%02h, received 0x%02h", data, rx_data);
            fail_count++;
        end
    endtask

    initial begin
        $dumpfile("dump.vcd"); $dumpvars(0, tb_uart);
        tx_valid = 0; tx_data = '0;
        repeat(5) @(posedge clk); rst_n = 1;
        repeat(5) @(posedge clk);
        send_byte(8'hA5);
        send_byte(8'h3C);
        send_byte(8'hFF);
        send_byte(8'h00);
        $display("\n=== %0d passed, %0d failed ===", pass_count, fail_count);
        if (fail_count > 0) $finish(1); else $finish(0);
    end
endmodule
