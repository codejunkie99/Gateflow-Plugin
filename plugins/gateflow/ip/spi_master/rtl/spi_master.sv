module spi_master #(
    parameter int CLK_DIV    = 4,
    parameter int DATA_WIDTH = 8
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  cpol,
    input  logic                  cpha,
    input  logic [DATA_WIDTH-1:0] tx_data,
    input  logic                  start,
    output logic [DATA_WIDTH-1:0] rx_data,
    output logic                  busy,
    output logic                  done,
    output logic                  sclk,
    output logic                  mosi,
    input  logic                  miso,
    output logic                  cs_n
);
    localparam int CNT_W = $clog2(CLK_DIV);
    logic [CNT_W-1:0] clk_cnt;
    logic [$clog2(DATA_WIDTH):0] bit_cnt;
    logic [DATA_WIDTH-1:0] shift_tx, shift_rx;
    logic running, sclk_int;

    assign cs_n = !running;
    assign sclk = running ? (sclk_int ^ cpol) : cpol;
    assign mosi = shift_tx[DATA_WIDTH-1];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            running  <= 1'b0; busy <= 1'b0; done <= 1'b0;
            sclk_int <= 1'b0; clk_cnt <= '0; bit_cnt <= '0;
            shift_tx <= '0; shift_rx <= '0; rx_data <= '0;
        end else begin
            done <= 1'b0;
            if (!running && start) begin
                running  <= 1'b1; busy <= 1'b1;
                shift_tx <= tx_data; shift_rx <= '0;
                bit_cnt  <= '0; clk_cnt <= '0; sclk_int <= 1'b0;
            end else if (running) begin
                if (clk_cnt == CLK_DIV[CNT_W-1:0] - 1) begin
                    clk_cnt  <= '0;
                    sclk_int <= !sclk_int;
                    if (sclk_int == cpha) begin
                        shift_rx <= {shift_rx[DATA_WIDTH-2:0], miso};
                    end else begin
                        if (bit_cnt == DATA_WIDTH[$clog2(DATA_WIDTH):0]) begin
                            running <= 1'b0; busy <= 1'b0; done <= 1'b1;
                            rx_data <= {shift_rx[DATA_WIDTH-2:0], miso};
                        end else begin
                            shift_tx <= {shift_tx[DATA_WIDTH-2:0], 1'b0};
                            bit_cnt  <= bit_cnt + 1'b1;
                        end
                    end
                end else clk_cnt <= clk_cnt + 1'b1;
            end
        end
    end
endmodule
