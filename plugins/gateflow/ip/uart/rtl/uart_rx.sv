module uart_rx #(
    parameter int CLK_FREQ  = 100_000_000,
    parameter int BAUD_RATE = 115200
) (
    input  logic       clk,
    input  logic       rst_n,
    input  logic       rx_in,
    output logic [7:0] rx_data,
    output logic       rx_valid
);
    localparam int CLKS_PER_BIT = CLK_FREQ / BAUD_RATE;
    localparam int CNT_W = $clog2(CLKS_PER_BIT);

    typedef enum logic [1:0] {IDLE, START, DATA, STOP} state_t;
    state_t state;
    logic [CNT_W-1:0] clk_cnt;
    logic [2:0] bit_idx;
    logic [7:0] rx_shift;
    logic [1:0] rx_sync;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) rx_sync <= 2'b11;
        else rx_sync <= {rx_sync[0], rx_in};

    wire rx_filtered = rx_sync[1];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state    <= IDLE;
            rx_valid <= 1'b0;
            rx_data  <= '0;
            clk_cnt  <= '0;
            bit_idx  <= '0;
            rx_shift <= '0;
        end else begin
            rx_valid <= 1'b0;
            unique case (state)
                IDLE: if (!rx_filtered) begin
                    state   <= START;
                    clk_cnt <= '0;
                end
                START: begin
                    if (clk_cnt == (CLKS_PER_BIT[CNT_W-1:0] >> 1)) begin
                        if (!rx_filtered) begin
                            clk_cnt <= '0;
                            bit_idx <= '0;
                            state   <= DATA;
                        end else state <= IDLE;
                    end else clk_cnt <= clk_cnt + 1'b1;
                end
                DATA: begin
                    if (clk_cnt == CLKS_PER_BIT[CNT_W-1:0] - 1) begin
                        clk_cnt <= '0;
                        rx_shift[bit_idx] <= rx_filtered;
                        if (bit_idx == 3'd7) state <= STOP;
                        else bit_idx <= bit_idx + 1'b1;
                    end else clk_cnt <= clk_cnt + 1'b1;
                end
                STOP: begin
                    if (clk_cnt == CLKS_PER_BIT[CNT_W-1:0] - 1) begin
                        rx_valid <= rx_filtered;
                        rx_data  <= rx_shift;
                        state    <= IDLE;
                    end else clk_cnt <= clk_cnt + 1'b1;
                end
            endcase
        end
    end
endmodule
