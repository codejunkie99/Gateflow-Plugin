module debouncer #(
    parameter int CLK_FREQ    = 100_000_000,
    parameter int DEBOUNCE_MS = 20
) (
    input  logic clk,
    input  logic rst_n,
    input  logic btn_in,
    output logic btn_out,
    output logic btn_rise,
    output logic btn_fall
);
    localparam int COUNT_MAX = CLK_FREQ / 1000 * DEBOUNCE_MS;
    localparam int CNT_W = $clog2(COUNT_MAX + 1);

    logic [CNT_W-1:0] counter;
    logic btn_sync, btn_prev;

    // 2FF synchronizer
    logic [1:0] sync_reg;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) sync_reg <= '0;
        else sync_reg <= {sync_reg[0], btn_in};
    assign btn_sync = sync_reg[1];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter  <= '0;
            btn_out  <= 1'b0;
            btn_prev <= 1'b0;
        end else begin
            btn_prev <= btn_out;
            if (btn_sync != btn_out) begin
                if (counter == COUNT_MAX[CNT_W-1:0])  begin
                    btn_out <= btn_sync;
                    counter <= '0;
                end else begin
                    counter <= counter + 1'b1;
                end
            end else begin
                counter <= '0;
            end
        end
    end

    assign btn_rise = btn_out && !btn_prev;
    assign btn_fall = !btn_out && btn_prev;
endmodule
